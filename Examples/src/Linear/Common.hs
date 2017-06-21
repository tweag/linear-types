{-# LANGUAGE GADTs #-}

module Linear.Common where

-- * Unrestricted

data Unrestricted a where
    Unrestricted :: a -> Unrestricted a
  deriving (Show,Eq)

getUnrestricted :: Unrestricted a ⊸ a
getUnrestricted (Unrestricted x) = x

mapU :: (a ⊸ b) -> Unrestricted a ⊸ Unrestricted b
mapU f (Unrestricted a) = Unrestricted (f a)

forceUnrestricted :: Unrestricted a ⊸ Unrestricted a
forceUnrestricted (Unrestricted a) = Unrestricted a
