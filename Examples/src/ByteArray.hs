module ByteArray where

import Linear.Std

type WByteArray = ()
type ByteArray = ()

alloc :: Int -> (WByteArray ⊸ Unrestricted b) ⊸ Unrestricted b
alloc = undefined

writeWord :: Word -> WByteArray ⊸ ()
writeWord = undefined

freeze :: WByteArray ⊸ Unrestricted ByteArray
freeze = undefined

index :: ByteArray -> Word -> a
index = undefined
