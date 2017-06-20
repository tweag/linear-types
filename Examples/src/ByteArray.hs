{-# LANGUAGE BangPatterns #-}

module ByteArray where

import Data.ByteString (ByteString)
import qualified Data.ByteString as ByteString
import qualified Data.ByteString.Unsafe as ByteString (unsafePackMallocCStringLen)
import Data.Word
import Foreign.C.String
import Foreign.Storable
import Linear.Std
import Linear.Unsafe
import System.IO.Unsafe (unsafeDupablePerformIO)

data WByteArray = WBA { pos::CString, orig::CString, stored::Int, rem::Int }
type ByteArray = ByteString

alloc :: Int -> (WByteArray ⊸ Unrestricted b) ⊸ Unrestricted b
alloc = undefined

writeByte :: Word8 -> WByteArray ⊸ WByteArray
writeByte = undefined

writeStorable :: Storable a => a -> WByteArray ⊸ WByteArray
writeStorable = undefined

freeze :: WByteArray ⊸ Unrestricted ByteArray
freeze wba =
    pack (project (promote wba))
  where
    project :: Unrestricted WByteArray ⊸ Unrestricted CStringLen
    project (Unrestricted (WBA{orig=str, stored=len})) = Unrestricted (str,len)

    promote :: WByteArray ⊸ Unrestricted WByteArray
    promote w = unsafeUnrestricted w

    pack :: Unrestricted CStringLen ⊸ Unrestricted ByteArray
    pack (Unrestricted cstr) = Unrestricted $ unsafeDupablePerformIO $
        ByteString.unsafePackMallocCStringLen cstr

index :: ByteArray -> Int -> Word8
index = undefined
