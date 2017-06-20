{-# LANGUAGE GADTs #-}

module Linear.Common where

-- * Unrestricted

data Unrestricted a where
    Unrestricted :: a -> Unrestricted a
  deriving (Show,Eq)

getUnrestricted :: Unrestricted a ⊸ a
getUnrestricted (Unrestricted x) = x
