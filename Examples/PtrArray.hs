{-# LANGUAGE TypeOperators, GADTs #-}
module PtrArray where

import Foreign hiding (free)
import qualified Foreign
import Foreign.Marshal.Array
import Foreign.C
import System.IO.Unsafe


-- Broken man's linear types.
type a ⊗ b = (a,b)
type a ⊸ b = a -> b

infixr ⊸
type Effect = IO () -- for simplicity
-- instance Monoid Effect

type N a = a ⊸ Effect

newtype Bang a = Bang { unBang :: a }


data MAr a = MAr {-ω-}Int {-ω-}(Ptr (Ptr a))

newtype Ar a = Ar (MAr a)

class Data a where
  move :: a -> Bang a
  free :: a ⊸ ()
instance Data CChar where
  move x = Bang x
  free x = ()

withNewAr :: Int -> (MAr a ⊸ Bang k) ⊸ k
withNewAr n f = unBang $ unsafePerformIO $
  allocaArray n (return . f . MAr n)

updateAr :: Int -> Ptr a -> MAr a ⊸ MAr a
updateAr n byte (MAr size ar) = unsafePerformIO $ do
  pokeElemOff ar n byte
  return $ MAr size ar

freeAr :: MAr a ⊸ ()
freeAr (MAr _ ar) = unsafePerformIO $ Foreign.free ar

freezeAr :: MAr a ⊸ Bang (Ar a)
freezeAr (MAr size ar) = Bang (Ar (MAr size ar))

indexAr :: Int -> Ar a -> Ptr a
indexAr i (Ar (MAr size ar)) = unsafePerformIO $
  peekElemOff ar i

{- ex = withNewByteArray 3 $ \ar ->
  let ar' = updateByteArray 1 64 ar
      (Bang ar'') = freezeByteArray ar'
  in indexByteArray 1 ar'' -}
