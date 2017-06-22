{-# LANGUAGE BangPatterns #-}

module ByteArray where

import Data.ByteString (ByteString)
-- import qualified Data.ByteString as ByteString
import qualified Data.ByteString.Unsafe as ByteString (unsafePackMallocCStringLen, unsafeUseAsCString)
import Data.Word
import Foreign.C.String
import Foreign.Marshal.Alloc
import Foreign.Ptr
import Foreign.Storable
import Linear.Std
import Linear.Unsafe
import Prelude hiding (rem,($))
import System.IO.Unsafe (unsafeDupablePerformIO)


data WByteArray = WBA { pos :: !CString, orig :: !CString, stored :: !Int, rem :: !Int }

-- Todo: @alloc@ should handle exception and free the pointer it allocates.
alloc :: Int -> (WByteArray ⊸ Unrestricted b) ⊸ Unrestricted b
alloc i f = forceUnrestricted $ f $ unsafeDupablePerformIO $ do
  str <- mallocBytes i -- Remark: can't use @alloca@ as the pointer will usually survive the scope
  return $! WBA { pos = str, orig = str, stored = 0, rem = i }

writeByte :: Word8 -> WByteArray ⊸ WByteArray
writeByte = writeStorable


writeStorable :: Storable a => a -> WByteArray ⊸ WByteArray
writeStorable obj wbarr = write (unsafeUnrestricted wbarr)
  where
    write :: Unrestricted WByteArray ⊸ WByteArray
    write (Unrestricted wba) = wba `seq` unsafeDupablePerformIO $ do
      let size = sizeOf obj
      poke (castPtr (pos wba)) obj
      let newPos = pos wba `plusPtr` size -- no alignment is done because it's hard to read back
      let sizeStored = newPos `minusPtr` pos wba
      return $! wba { pos = newPos, rem = rem wba - sizeStored, stored = stored wba + sizeStored }

freeze :: WByteArray ⊸ Unrestricted ByteString
freeze wba =
    pack (project (unsafeUnrestricted wba))
  where
    project :: Unrestricted WByteArray ⊸ Unrestricted CStringLen
    project (Unrestricted (WBA{orig=str, stored=len})) = Unrestricted (str,len)

    pack :: Unrestricted CStringLen ⊸ Unrestricted ByteString
    pack (Unrestricted cstr) = Unrestricted $ unsafeDupablePerformIO $
        ByteString.unsafePackMallocCStringLen cstr

-- TODO: bound checking
headStorable :: Storable a => ByteString -> a
headStorable bs = unsafeDupablePerformIO $
    ByteString.unsafeUseAsCString bs $ \ cstr ->
      peek (castPtr cstr)
