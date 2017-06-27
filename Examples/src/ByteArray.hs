
-- | An interface for mutable byte arrays, handled linearly.

{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE CPP #-}
-- {-# LANGUAGE GeneralizedNewtypeDeriving #-}

module ByteArray
    ( WByteArray,
      alloc, freeze, headStorable, 
      withHeadStorable, withHeadStorable2,
      writeStorable, writeByte,
      -- * Monomorphic interface
      headWord8, headWord8',
      headInt,
                   
      -- * Monadic interface
      ReadM, runReadM, isEndM, headStorableM, headStorableOfM,

      -- * Tests
      prop_counter, t1, allocWBA
    )
    where

import Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Unsafe as ByteString (unsafePackMallocCStringLen, unsafeUseAsCString)
import Data.Word
import Foreign.C.String
import Foreign.Marshal.Alloc (mallocBytes, malloc, free)
import Foreign.Ptr
import Foreign.Storable
import Foreign.C.Types
import Linear.Std
import Linear.Unsafe
import Prelude hiding (rem,($))
import System.IO.Unsafe (unsafePerformIO, unsafeDupablePerformIO)

-- import GHC.IO
--import GHC.Prim (RealWorld, State#)
import GHC.Prim (Word#, Char#, Int#, plusAddr#, indexIntOffAddr#,
                 indexCharOffAddr#, ord#, int2Word#)
import GHC.Magic (runRW#)
import GHC.ForeignPtr (ForeignPtr(..))
import Data.ByteString.Internal (ByteString(..))
import GHC.Int (Int(..))
import GHC.Word (Word8(..))
import Data.IORef
---------------------------------

-- type Token = State# RealWorld


{-# INLINE incCounter #-}
{-# INLINE readCounter #-}
{-# INLINE newCounter #-}
{-# INLINE freeCounter #-}
incCounter  :: MutCounter -> Int -> IO ()
readCounter :: MutCounter -> IO Int
newCounter  :: IO MutCounter
freeCounter :: MutCounter -> IO ()

#if 1
-- | An unboxed mutable counter.  Could use an Unboxed vector.
type MutCounter = Ptr Int
incCounter c m = do n <- peek c; poke c (n+m)
readCounter    = peek
newCounter  = do (c::Ptr Int) <- malloc
                 poke c (0::Int)
                 return c
freeCounter = free 
#else
-- SAFER version, debugging:
type MutCounter = IORef Int
incCounter c m = modifyIORef' c (+m)
readCounter    = readIORef
newCounter     = newIORef 0
freeCounter _ = return ()
#endif

              
------------------------------------------------------------

-- | A monad to /aggregate/ peek operations on a byte buffer.  This is
--  for optimization purposes.
--
--  This version does not allow any memory to be freed until the whole
--  byte buffer is read.
newtype ReadM a = ReadM { unReadM :: CString -> MutCounter -> Int -> IO a }
    -- ^ Takes an offset into the bytes, total size, and returns a new
    -- offset at each step.
    
--  deriving (Monad, Functor, Applicative)

instance Functor ReadM where

instance Applicative ReadM where

instance Monad ReadM where
    return x = ReadM (\_ _ _ -> return x)
    ReadM f1 >>= f2 =
      ReadM $ \cstr offset sz ->
        do x <- f1 cstr offset sz 
           let ReadM f3 = f2 x
           f3 cstr offset sz


-- | Are we at the end of the stream?  Have we read all available bytes?
isEndM :: ReadM Bool
isEndM = ReadM $ \ _ off size -> do
           pos <- readCounter off
           return $! pos == size

{-# INLINE runReadM #-}
-- | Read from a particular byte array.
runReadM :: ByteString -> ReadM a -> a
runReadM bs (ReadM fn) = unsafeDupablePerformIO $ 
   ByteString.unsafeUseAsCString bs $ \ cstr ->
      do cntr <- newCounter
         fn cstr cntr (BS.length bs)

-- runReadM :: WByteArray -> ReadM a -> a
-- runReadM ba (ReadM fn) = unsafeDupablePerformIO (fn ba)

                         
data WByteArray = WBA { offset :: !MutCounter
                      , bytes  :: !CString
                      }

instance Show WByteArray where
  show WBA{offset,bytes} =
    let off = unsafePerformIO (readCounter offset) in
    "WByteArray <offset "++ show off ++ ">"
    -- "WByteArray <"++show bytes ++ ", offset at "++show offset++" = "++ show off ++ ">"
                
{-# NOINLINE alloc #-}
-- | Allocate and use a mutable, linear byte array.
alloc :: Int -> (WByteArray ⊸ Unrestricted b) ⊸ Unrestricted b
alloc i f = forceUnrestricted $ f $ unsafePerformIO (allocWBA i)

allocWBA :: Int -> IO WByteArray
allocWBA i= do              
     str <- mallocBytes (i) -- Remark: can't use @alloca@ as the pointer will usually survive the scope
     -- pokeElemOff str i (0::CChar) -- Null terminated.  But there may be other zeros!  Not a real CString.
     cnt <- newCounter
     return $! WBA{ offset = cnt
                  , bytes  = str
                  }
-- Todo: @alloc@ should handle exception and free the pointer it allocates.


{-# INLINE writeByte #-}
-- | Write a single byte to the end of a byte array.
writeByte :: Word8 -> WByteArray ⊸ WByteArray
writeByte = writeStorable

{-# INLINE writeStorable #-}
-- | Write a storable value to the end of a byte array.
writeStorable :: Storable a => a -> WByteArray ⊸ WByteArray
writeStorable = unsafeCastLinear writeStorable'

{-# INLINE writeStorable' #-}                 
writeStorable' :: Storable a => a -> WByteArray -> WByteArray
writeStorable' obj wbarr@WBA{offset,bytes} =
    unsafeDupablePerformIO effect `seq` wbarr
  where
   effect = do i <- readCounter offset
               poke (castPtr bytes `plusPtr` i) obj
               incCounter offset (sizeOf obj)

{-# NOINLINE freeze #-}
freeze :: WByteArray ⊸ Unrestricted ByteString
freeze = unsafeCastLinear f
  where
   f WBA{offset,bytes} = unsafeUnrestricted $ unsafePerformIO $ do
     sz <- readCounter offset
     freeCounter offset
     ByteString.unsafePackMallocCStringLen (bytes,sz)

--    pack (project (unsafeUnrestricted wba))
--    pack (project (unsafeUnrestricted wba))
--   where
--    project :: Unrestricted WByteArray ⊸ Unrestricted CStringLen
--    project (Unrestricted (WBA{orig, pos})) = Unrestricted (orig,pos `minusPtr` orig)

    -- pack :: Unrestricted CStringLen ⊸ Unrestricted ByteString
    -- pack (Unrestricted cstr) = Unrestricted $ unsafePerformIO $ do
    --     freeCounter 
    --     ByteString.unsafePackMallocCStringLen cstr

{-# INLINE headStorable #-}
-- TODO: bound checking
headStorable :: Storable a => ByteString -> a
headStorable bs = unsafeDupablePerformIO $
               ByteString.unsafeUseAsCString bs $ \ cstr -> 
                   peek (castPtr cstr)

{-# INLINE headStorableOfM #-}
-- TODO: bound checking
-- | Read from the head of the given bytestring.
headStorableOfM :: Storable a => ByteString -> ReadM a
headStorableOfM bs = ReadM $ \_ _ _ ->
                       ByteString.unsafeUseAsCString bs $ \ cstr -> 
                               peek (castPtr cstr)

{-# INLINE headWord8' #-}
-- | An example of how to read directly from a ptr without boxing the result.
headWord8' :: ByteString -> Char#
headWord8' (PS (ForeignPtr addr _) (I# offset) _)=
    indexCharOffAddr# (plusAddr# addr offset) 0#    
--    (error "FINISHMe -- read from Addr# directly" :: Word#)

{-# INLINE headWord8 #-}
headWord8 :: ByteString -> Word8
headWord8 (PS (ForeignPtr addr _) (I# offset) _)=
    W8# (int2Word# (ord# (indexCharOffAddr# (plusAddr# addr offset) 0#)))

{-# INLINE headInt #-}
headInt :: ByteString -> Int
headInt (PS (ForeignPtr addr _) (I# offset) _) =
    I# (indexIntOffAddr# (plusAddr# addr offset) 0# )


{-# INLINE headStorableM #-}
-- | Read from the bytestring stored in the monad.
headStorableM :: forall a . Storable a => ReadM a
headStorableM = ReadM $ \cstr cntr _size -> -- TODO!  BOUNDS CHECK
                    do offset <- readCounter cntr
                       !x <- peek (castPtr (cstr `plusPtr` offset))
                       incCounter cntr (sizeOf (undefined::a))
                       return x

{-# INLINE withHeadStorable #-}
-- | An alternative to @headStorable@ which permits different compiler
-- optimizations.
withHeadStorable :: Storable a => ByteString -> (a -> b) -> b
withHeadStorable bs f = unsafeDupablePerformIO $
    ByteString.unsafeUseAsCString bs $ \ cstr ->  do
      !x <- peek (castPtr cstr)
      return $! f x

{-# INLINE withHeadStorable2 #-}
-- | An alternative to @headStorable@ which permits different compiler
-- optimizations.
withHeadStorable2 :: Storable a => ByteString -> (a -> (# b1, b2 #)) -> (# b1, b2 #)
withHeadStorable2 bs f = (# x, y #)
  where
   (x,y) = unsafeDupablePerformIO $
    ByteString.unsafeUseAsCString bs $ \ cstr ->  do
      !r <- peek (castPtr cstr)
      case f r of
        (# a,b #) -> return (a,b)  -- Sigh... 


------------------------------------------------------------

t1 = alloc 128 (\w -> unsafeUnrestricted w)

{-# NOINLINE prop_counter #-}
prop_counter :: Int -> Bool
prop_counter n = unsafePerformIO (do c <- newCounter
                                     go c n)
                 == n
 where
   go c 0 = readCounter c
   go c n = do incCounter c 1
               go c (n-1)
