module FreezeArray where

import Linear.Std
import Prelude hiding (($))

data Array a = Array -- TODO
data MArray a = MArray -- TODO


newMArray :: Int -> a -> (MArray a ⊸ Unrestricted b) ⊸ Unrestricted b
newMArray = error "TODO: FreezeArray.newMArray"

write :: MArray a ⊸ Int -> a -> MArray a
write = error "TODO: FreezeArray.write"

read :: MArray a ⊸ Int -> (MArray a, Unrestricted a)
read = error "TODO: FreezeArray.read"

freeze :: MArray a ⊸ Unrestricted (Array a)
freeze = error "TODO: FreezeArray.freeze"

index :: Array a -> Int -> a
index = error "TODO: FreezeArray.index"
