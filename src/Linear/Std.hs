-- | Standard library functions with linear types.

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

-- * Linear version of some standard function

($) :: (a⊸b) ⊸ a ⊸ b
($) f x = f x

infixr 0 $

const :: a ⊸ b -> a
const x _ = x

swap :: (a,b) ⊸ (b,a)
swap (x,y) = (y,x)

-- | As long as this function is only for the sake of demonstration, let's give
-- it a different name than the prelude one so that it doesn't force hiding
-- Prelude's foldl.
foldlL :: (a ⊸ b ⊸ a) -> a ⊸ [b] ⊸ a
foldlL _reduce acc [] = acc
foldlL reduce acc (a:l) = foldlL reduce (reduce acc a) l

-- * Comonoids and data types
--
-- The classes and instances below are not used in the artifact, they are
-- important concepts when programming with linear types. So they are included
-- for reference.

-- | The laws of comonoids are dual to that of monoid:
--
-- * first drop (dup a) ≃ a
-- * first dup (dup a) ≃ (second dup (dup a))
-- * …
--
-- Comonoids support duplication linearly. For instance by copy, like Bool,
-- below, or because @a@ is really unrestricted, like Unrestricted below.
class Comonoid a where
  drop :: a ⊸ ()
  dup :: a ⊸ (a,a)

-- | A natural extension of Comonoid where the "copy" is unrestricted
class Comonoid a => UComonoid a where
  move :: a ⊸ Unrestricted a

instance Comonoid Bool where
  drop True = ()
  drop False = ()

  dup True = (True,True)
  dup False = (False,False)

instance Comonoid (Unrestricted a) where
  drop (Unrestricted _) = ()
  dup (Unrestricted x) = (Unrestricted x, Unrestricted x)

instance UComonoid (Unrestricted a) where
  move (Unrestricted x) = Unrestricted (Unrestricted x)
