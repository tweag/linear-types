{-# LANGUAGE GADTs #-}

module Linear.Common where

-- * Unrestricted

data Unrestricted a where
    Unrestricted :: a -> Unrestricted a
  deriving (Show,Eq)

{-# INLINE getUnrestricted #-}
getUnrestricted :: Unrestricted a ⊸ a
getUnrestricted (Unrestricted x) = x

{-# INLINE mapU #-}
mapU :: (a ⊸ b) -> Unrestricted a ⊸ Unrestricted b
mapU f (Unrestricted a) = Unrestricted (f a)

{-# INLINE forceUnrestricted #-}
forceUnrestricted :: Unrestricted a ⊸ Unrestricted a
forceUnrestricted (Unrestricted a) = Unrestricted a

linerror :: String -> b ⊸ a
linerror = error
