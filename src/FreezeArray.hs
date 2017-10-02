{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE LambdaCase #-}

module FreezeArray where

import Linear.Std
import Prelude hiding (($))

data Array a = Array -- TODO
data MArray a = MArray -- TODO


newMArray :: Int -> a -> (MArray a ⊸ Unrestricted b) ⊸ Unrestricted b
newMArray = error "TODO: FreezeArray.newMArray"

lengthM :: MArray a ⊸ (MArray a, length)
lengthM = error "TODO: FreezeArray.lengthM"

write :: MArray a ⊸ Int -> a -> MArray a
write = error "TODO: FreezeArray.write"

read :: MArray a ⊸ Int -> (MArray a, Unrestricted a)
read = error "TODO: FreezeArray.read"

freeze :: MArray a ⊸ Unrestricted (Array a)
freeze = error "TODO: FreezeArray.freeze"

index :: Array a -> Int -> a
index = error "TODO: FreezeArray.index"


-- * Builder API

data BuilderInstr a r
  = Step ((a -> Builder a) ⊸ r)
  | Freeze (Unrestricted (Array a) ⊸ r)

newtype Builder a = Builder (forall r. BuilderInstr a r ⊸ r)

push :: a -> Builder a ⊸ Builder a
push a (Builder exec) = exec $ Step (\ step -> step a)

build :: Int -> a -> (Builder a ⊸ Unrestricted b) ⊸ Unrestricted b
build chunkSize initVal k =
    newMArray chunkSize initVal $ \ marr ->
      k (mkBuilder 0 marr)

  where
    mkBuilder :: Int -> MArray a ⊸ Builder a
    mkBuilder i marr = Builder (\case   -- No ($) because the linear ($) doesn't work with polymorphic types
      Step doStep -> doStep $ \ a ->
        mkBuilder (i+1) (write marr i a)
      Freeze doFreeze -> doFreeze (freeze marr))
