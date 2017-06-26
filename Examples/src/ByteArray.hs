
-- | An interface for mutable byte arrays, handled linearly.

{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
-- {-# LANGUAGE GeneralizedNewtypeDeriving #-}

module ByteArray
    ( WByteArray,
      alloc, freeze, headStorable, 
      withHeadStorable, withHeadStorable2,
      writeStorable, writeByte,
      -- * Monadic interface
      ReadM, runReadM, isEndM, headStorableM, headStorableOfM
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
-- import GHC.Prim (RealWorld, State#)
---------------------------------

-- type Token = State# RealWorld

-- | An unboxed mutable counter.  Could use an Unboxed vector.
type MutCounter = Ptr Int

{-# INLINE incCounter #-}
incCounter :: MutCounter -> Int -> IO ()
incCounter c m = do n <- peek c
                    poke c (n+m)

{-# INLINE readCounter #-}
readCounter :: MutCounter -> IO Int
readCounter = peek

{-# INLINE newCounter #-}
newCounter :: IO MutCounter
newCounter = do c <- malloc
                poke c 0
                return c

{-# INLINE freeCounter #-}
freeCounter :: MutCounter -> IO ()
freeCounter = free 
    
------------------------------------------------------------

-- | A monad to /aggregate/ peek operations on a byte buffer.  This is
--  for optimization purposes.
--
--  This version does not allow any memory to be freed until the whole
--  byte buffer is read.
newtype ReadM a = ReadM { unReadM :: CString -> Int -> Int -> IO (a, Int) }
    -- ^ Takes an offset into the bytes, total size, and returns a new
    -- offset at each step.
    
--  deriving (Monad, Functor, Applicative)

instance Functor ReadM where

instance Applicative ReadM where

instance Monad ReadM where
    return x = ReadM (\_ off _ -> return (x, off))
    ReadM f1 >>= f2 =
      ReadM $ \cstr offset sz ->
        do (x,off2) <- f1 cstr offset sz 
           let ReadM f3 = f2 x
           f3 cstr off2 sz


-- | Are we at the end of the stream?  Have we read all available bytes?
isEndM :: ReadM Bool
isEndM = ReadM (\ _ off size -> (return $! (, off) $! off == size))

{-# INLINE runReadM #-}
-- | Read from a particular byte array.
runReadM :: ByteString -> ReadM a -> a
runReadM bs (ReadM fn) = unsafeDupablePerformIO $ 
   ByteString.unsafeUseAsCString bs $ \ cstr ->
      do (x,_) <- fn cstr 0 (BS.length bs)
         return x

-- runReadM :: WByteArray -> ReadM a -> a
-- runReadM ba (ReadM fn) = unsafeDupablePerformIO (fn ba)

                         
data WByteArray = WBA { offset :: !MutCounter
                      , bytes  :: !CString
                      }

{-# NOINLINE alloc #-}
-- | Allocate and use a mutable, linear byte array.
alloc :: Int -> (WByteArray ⊸ Unrestricted b) ⊸ Unrestricted b
alloc i f = forceUnrestricted $ f $ unsafePerformIO $ do              
     str <- mallocBytes (i+1) -- Remark: can't use @alloca@ as the pointer will usually survive the scope
     pokeElemOff str i (0::CChar) -- Null terminated.  But there may be other zeros!  Not a real CString.
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
headStorableOfM bs = ReadM $ \_ off _ ->
                     do x <- ByteString.unsafeUseAsCString bs $ \ cstr -> 
                               peek (castPtr cstr)
                        return (x , off)

{-# INLINE headStorableM #-}
-- | Read from the bytestring stored in the monad.
headStorableM :: forall a . Storable a => ReadM a
headStorableM = ReadM $ \cstr offset size -> -- TODO!  BOUNDS CHECK
                    do x <- peek (castPtr (cstr `plusPtr` offset))
                       return $! (x,)
                              $! (offset + sizeOf (undefined::a))

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

