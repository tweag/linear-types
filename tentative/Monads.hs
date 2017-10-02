{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
module Monads where


{-
Making bind linear in its first and second argument appear to prevent certain existing use of monads:
it seem that we need to reuse the continuation several times, in general, to
map over the previous list of results.

Yet, even lists can be made a monad if properly generalised, see below.
  
-}

data Multiplicity = One | Omega | Multiplicity :× Multiplicity 

-- In this file we evaluate what could Monad look like with linear types.
-- the contender is:

-- Constraint: (forall p. Functor (m p)) => Monad' m

class Monad' m where
  join :: m p (m q a) -> m (p:×q) a
  fmap' :: (a ⊸ b) -> (m p) a ⊸ (m p) b
  bind :: m p a ⊸ ((a ->{-p-} m q b) ⊸ m (p:×q) b)
  bind m f = join (fmap' f m)

type a ⊸ b = a -> b

newtype MuList (p::Multiplicity) a = Fold {fold ::{-1-} forall b. (a ->{-p-} (b ⊸ b)) -> (b ⊸ b)}

-- fold :: MuList {-p-} a ⊸ forall b. (a ->{-p-} (b ⊸ b)) -> (b ⊸ b)

joinMuList :: MuList p (MuList q a) -> MuList (p:×q) a
joinMuList (Fold build{-1-}) = Fold $ \cons{-::_w (a ->{-pq-} (b ⊸ b)) -} ->
    build (\xs{-::_p MuList {-q-} a -} zero{-1-} -> fold xs (\y{-q-} ys{-1-} -> cons y ys) zero)

-- xs ::_p MuList q a
-- fold xs ::_p forall b. (a ->q (b ⊸ b)) -> (b ⊸ b)


data List (p::Multiplicity) a where
  Nil :: List p a
  Cons :: a ->{-p-} List p a ->{-1-} List p a


append :: List p a ->{-1-} List p a ->{-1-} List p a
append = _

joinList :: List p (List q a) -> List (p:×q) a
joinList Nil = Nil
joinList (Cons x xs) = append x (joinList xs)


-- Local Variables:
-- dante-project-root: "."
-- End:

