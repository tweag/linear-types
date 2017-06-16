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
  Unrestricted $ unsafeDupablePerformIO $
    ByteString.unsafePackMallocCStringLen (orig,len)
  where
    project (WBA{orig=orig, stored=len}) = (orig,len)
    promote :: WByteArray ⊸ Unrestricted (orig,len)
    promote wba = undefined

index :: ByteArray -> Int -> Word8
index = undefined
