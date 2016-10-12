{-# LANGUAGE TypeOperators, GADTs #-}
module StorageServer where

-- This module shows an example of a more realistic server
-- implementation: a storage server.

-- We show in particular how to store long-term data in the linear
-- heap.

import Data.Monoid

-- Broken man's linear types.
type a ⊗ b = (a,b)
type a ⊸ b = a -> b

infixr ⊸
type Effect = IO () -- for simplicity
-- instance Monoid Effect

type N a = a ⊸ Effect

-- | A linear version of Maybe
data Perhaps v where
  No :: Perhaps v
  Indeed :: v {-1-}-> Perhaps v

-- Read the "Protocol.hs" file first for an introduction to protocols.
data Client k v
  = Store {-ω-}k {-1-}v {-1-}(N (Server k v)) -- (1)
  | Get {-ω-}k {-1-}(N (Perhaps v ⊗ (Server k v)))
  | Terminate

type Server k v = N (Client k v)

-- | A storage server implemented in memory
basicStorageServer :: (Eq k, Dup v) => Storage k v ⊸ Server k v
basicStorageServer storage client = case client  of
  Store k v respond -> respond (basicStorageServer (Tray k v storage))
                       -- Exercise: discard 'old' entries to simulate a cache.
  Get k respond -> case find k storage of
    (x,storage') -> respond (x,basicStorageServer storage')
  Terminate -> return ()

-- | Storage sturucture.
data Storage k v where
  Empty :: Storage k v
  -- Tray :: k -> v ⊸ Storage k v ⊸ Storage k v -- GHC does not like this at the moment
  Tray :: {-ω-}k -> v {-1-}-> Storage k v {-1-}-> Storage k v
-- ... implemented as a list. In reality this should be more clever.

class Dup a where
  copy :: a -> (a⊗a)


find :: (Eq k, Dup v) => k -> Storage k v ⊸ (Perhaps v ⊗ Storage k v)
find _ Empty = (No,Empty)
find k (Tray k' v rest)                                          -- (1)
  | k == k' = case copy v of (v,v') -> (Indeed v',Tray k v rest) -- (2)
  | otherwise = case find k rest of
      (result,rest') -> (result,Tray k v rest')                  -- (2)

-- Remark on efficiency: (1) frees stuff from the heap and (2)
-- allocates the same amount. We can reasonably expect that an
-- optimizer will reuse the space instead of performing two inverse heap
-- manipulations.


-- In a production code, the server state will inevitably contain
-- references to (linear) contexts for database, disk, etc. See
-- "HaskellR.hs" for how such contexts are meant to be managed.

-- | Here we give an example of server combinators: we try to fetch
-- data from the first server, but if that fails we go for the second one.
-- We store always in both servers.
tieredStorageServer :: Dup v => Server k v -> Server k v -> Server k v
tieredStorageServer s1 s2 client = case client of
  Get k respond -> s1 $ Get k $ \mv -> case mv of
    (Indeed v,s1) -> respond (Indeed v,tieredStorageServer s1 s2)
    (No,s1) -> s2 $ Get k $ \mv -> case mv of
      (Indeed v,s2) -> respond (Indeed v,tieredStorageServer s1 s2)
      (No,s2) -> respond (No,tieredStorageServer s1 s2)
  Store k v respond -> let (v1,v2) = copy v in
    s1 $ Stoke k v1 $ \s1 ->
    s2 $ Store k v2 $ \s2 ->
    respond (tieredStorageServer s1 s2)


{- Thoughts about distributed computations

Distributable (N a) where
combine :: N a ⊸ N a  ⊸ N a
unit :: Index -> N a

Composition:

N(a⊗N b)

N(b⊗N c)


pipe :: N(b ⊗ N b)
pipe (b,nb) = nb b

chain :: N(a⊗N b) -> N(b⊗N c) -> N(a⊗N c)
chain p1 p2 (a,nc) =
  pipe $ \(b,nb) ->
  p1 (a,nb) >>
  p2 (b,nc)

-}
