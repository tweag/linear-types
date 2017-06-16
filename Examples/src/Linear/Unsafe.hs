{-# LANGUAGE GADTs #-}

module Linear.Unsafe where

import Linear.Common
import qualified Unsafe.Coerce as NonLinear

-- | Linearly typed @unsafeCoerce@
unsafeCoerce :: a ⊸ b
unsafeCoerce = NonLinear.unsafeCoerce NonLinear.unsafeCoerce

-- * Bypasses linearity constraints

data NotUnrestricted a where NotUnrestricted :: a ⊸ NotUnrestricted a

unsafeUnrestricted :: a ⊸ Unrestricted a
unsafeUnrestricted x = unsafeCoerce $ NotUnrestricted x

-- * Helpers to convert library functions to expose their linearity

unsafeCastLinear2 :: (a -> b -> c) ⊸ (a ⊸ b ⊸ c)
unsafeCastLinear2 = unsafeCoerce

unsafeCastLinear :: (a -> b) ⊸ (a ⊸ b)
unsafeCastLinear = unsafeCoerce
