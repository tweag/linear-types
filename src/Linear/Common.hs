-- | The root of the dependence hierarchy -- shared between Linear.Std and
-- Linear.Unsafe. This is reexported by Linear.Std.

{-# LANGUAGE GADTs #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE RankNTypes #-}

module Linear.Common where
import GHC.Types (Type, TYPE, RuntimeRep)
    
-- * Unrestricted

-- | The Unrestricted data type uses the GADT syntax with a standard arrow (->)
-- to indicate that its content is always unrestricted
data Unrestricted a where
    Unrestricted :: a -> Unrestricted a
  deriving Show

{-# INLINE getUnrestricted #-}
getUnrestricted :: Unrestricted a ⊸ a
getUnrestricted (Unrestricted x) = x

{-# INLINE mapU #-}
mapU :: (a ⊸ b) -> Unrestricted a ⊸ Unrestricted b
mapU f (Unrestricted a) = Unrestricted (f a)

{-# INLINE forceUnrestricted #-}
forceUnrestricted :: Unrestricted a ⊸ Unrestricted a
forceUnrestricted (Unrestricted a) = Unrestricted a

-- | A hard-coded size constant allocated for each regions
regionSize :: Int
regionSize = 500 *1000*1000
