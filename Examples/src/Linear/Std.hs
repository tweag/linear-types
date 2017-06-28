-- | Derived utilities that use the Unsafe bits.

{-# LANGUAGE GADTs #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE RankNTypes #-}

module Linear.Std (
  module Linear.Std, -- self
  module Linear.Common
) where

import GHC.Types (Int(..), Type, TYPE, RuntimeRep)
import Linear.Common
import Linear.Unsafe
import Prelude hiding (($))
import Debug.Trace
import System.IO.Unsafe(unsafePerformIO)

-- * Linear version of some standard function

($) :: (a⊸b) ⊸ a ⊸ b
($) f x = f x

infixr 0 $

const :: a ⊸ b -> a
const x _ = x

swap :: (a,b) ⊸ (b,a)
swap (x,y) = (y,x)

-- TODO: make strict
-- | As long as this function is only for the sake of demonstration, let's give
-- it a different name than the prelude one so that it doesn't force hiding
-- Prelude's foldl.
foldlL :: (a ⊸ b ⊸ a) -> a ⊸ [b] ⊸ a
foldlL _reduce acc [] = acc
foldlL reduce acc (a:l) = foldlL reduce (reduce acc a) l

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
      almostDropInt (I# _) = ()
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

-- | Trace a value in a linear context.
lintrace :: String -> a ⊸ a
lintrace str = trace str (\x -> x)
--    case unsafePerformIO (putStrLn str) of
--                    () -> x
