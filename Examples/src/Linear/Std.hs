{-# LANGUAGE GADTs #-}
{-# LANGUAGE MagicHash #-}

module Linear.Std (
  module Linear.Std, -- self
  module Linear.Common
) where

import GHC.Types (Int(..))
import Linear.Common
import Linear.Unsafe

-- * Linear version of some standard function

const :: a ⊸ b -> a
const x _ = x

swap :: (a,b) ⊸ (b,a)
swap (x,y) = (y,x)

-- * Comonoids and data types

-- | The laws of comonoids are dual to that of monoid:
--
-- * first drop (dup a) ≃ a
-- * first dup (dup a) ≃ (second dup (dup a))
-- * …
class Comonoid a where
  drop :: a ⊸ ()
  dup :: a ⊸ (a,a)

-- [aspiwack] I don't know that there is a standard notion for @move@.
class Comonoid a => UComonoid a where
  move :: a ⊸ Unrestricted a

instance Comonoid (Unrestricted a) where
  drop (Unrestricted _) = ()
  dup (Unrestricted x) = (Unrestricted x, Unrestricted x)

instance UComonoid (Unrestricted a) where
  move (Unrestricted x) = Unrestricted (Unrestricted x)


instance Comonoid Int where
  drop = unsafeCastLinear almostDropInt
    where
      -- it matters, for correctness, that the int is forced
      almostDropInt :: Int -> ()
      almostDropInt (I# i) = ()
  dup = unsafeCastLinear $ almostDupInt
    where
      -- it matters, for correctness, that the int is forced
      almostDupInt :: Int -> (Int,Int)
      almostDupInt (I# i) = (I# i, I# i)

instance UComonoid Int where
  move = unsafeCastLinear $ almostMoveInt
    where
      -- it matters, for correctness, that the int is forced
      almostMoveInt :: Int -> Unrestricted Int
      almostMoveInt (I# i) = (Unrestricted (I# i))
