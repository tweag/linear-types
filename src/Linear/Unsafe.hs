{-# LANGUAGE GADTs #-}

{-# LANGUAGE GADTs #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE RankNTypes #-}

module Linear.Unsafe where

import Linear.Common
import qualified Unsafe.Coerce as NonLinear

import GHC.Types (TYPE, RuntimeRep)

    
-- | Linearly typed @unsafeCoerce@
unsafeCoerce :: a ⊸ b
unsafeCoerce = NonLinear.unsafeCoerce NonLinear.unsafeCoerce

-- * Bypasses linearity constraints

data NotUnrestricted a where NotUnrestricted :: a ⊸ NotUnrestricted a

-- | @unsafeUnrestricted x@ can only work if all the effects hidden in `x` have
-- been run. Otherwise the effects may get duplicated. Make sure you only use it
-- for something that is fully evaluated or pass the unrestricted value to a
-- function which will ensure that the effects are not duplicated (for instance
-- a function that starts by fully evaluating its unrestricted argument).
unsafeUnrestricted :: a ⊸ Unrestricted a
unsafeUnrestricted x = unsafeCoerce $ NotUnrestricted x

-- * Helpers to convert library functions to expose their linearity

unsafeCastLinear2 :: (a -> b -> c) ⊸ (a ⊸ b ⊸ c)
unsafeCastLinear2 = unsafeCoerce

unsafeCastLinear :: forall (r1 :: RuntimeRep) (r2 :: RuntimeRep)
                           (a :: TYPE r1) (b :: TYPE r2) .
                    (a -> b) ⊸ (a ⊸ b)
unsafeCastLinear = unsafeCoerce
