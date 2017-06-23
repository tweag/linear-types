
-- | An interface for mutable byte arrays, handled linearly.

{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE NamedFieldPuns #-}

module ByteArray
    ( WByteArray, alloc, freeze, headStorable, writeStorable, writeByte )
    where

import Data.ByteString (ByteString)
-- import qualified Data.ByteString as ByteString
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
