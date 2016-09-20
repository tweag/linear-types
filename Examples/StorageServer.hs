{-# LANGUAGE TypeOperators, GADTs #-}
module StorageServer where

-- This module implements a storage server. The data is stored in the
-- linear heap.

-- Read the "Protocol" module first for an introduction to protocols.

import Data.Monoid

-- Broken man's linear types.
type a ⊗ b = (a,b)
type a ⊸ b = a -> b

infixr ⊸
type Effect = IO () -- for simplicity
-- instance Monoid Effect

type N a = a ⊸ Effect

data Perhaps v where
  No :: Perhaps v
  Indeed :: v {-1-}-> Perhaps v

data Client k v
  = Store {-ω-}k {-1-}v {-1-}(N (Server k v))
  | Get {-ω-}k {-1-}(N (Perhaps v ⊗ (Server k v)))
  | Terminate
type Server k v = N (Client k v)

-- List implementation. In reality this should be more clever.
data Storage k v where
  Empty :: Storage k v
  -- Compartment :: k -> v ⊸ Storage k v ⊸ Storage k v -- GHC does not like this at the moment
  Tray :: {-ω-}k -> v {-1-}-> Storage k v {-1-}-> Storage k v

class Dup a where
  copy :: a -> (a⊗a)

find :: (Eq k, Dup v) => k -> Storage k v ⊸ (Perhaps v ⊗ Storage k v)
find _ Empty = (No,Empty)
find k (Tray k' v rest)
  | k == k' = case copy v of (v,v') -> (Indeed v',Tray k v rest)
  | otherwise = case find k rest of
      (result,rest') -> (result,Tray k v rest')

basicStorageServer :: (Eq k, Dup v) => Storage k v -> Server k v
basicStorageServer storage client = case client  of
  Store k v respond -> respond (basicStorageServer (Tray k v storage))
  Get k respond -> case find k storage of
    (x,storage') -> respond (x,basicStorageServer storage')
  Terminate -> return ()


tieredStorageServer :: Server k v -> Server k v -> Server k v
tieredStorageServer s1 s2 client = case client of
  Get k respond -> s1 $ Get k $ \mv -> case mv of
    (Indeed v,s1) -> respond (Indeed v,tieredStorageServer s1 s2)
    (No,s1) -> s2 $ Get k $ \mv -> case mv of
      (Indeed v,s2) -> respond (Indeed v,tieredStorageServer s1 s2)
      (No,s2) -> respond (No,tieredStorageServer s1 s2)
  Store k v respond -> s2 $ Store k v $ \s2 -> respond (tieredStorageServer s1 s2)
