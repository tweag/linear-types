{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}

-- | This first version of the linear queue API is what appeared in the first draft of the paper:

module QueueRefImpl where

-- The two character token "-o" is not valid, so just use this to mark
-- linear arrows for now:
type (⊸) = (->)
infixr ⊸
type a ⊗ b = (a,b)

class Storabloid a where
  store :: a ⊸ a -- move to the linear heap (when called in a linear context)
  load :: a ⊸ Bang a -- move to the GC heap (and delete from the linear one)
  -- either of the above functions do nothing useful when called from a dynamic context.

storabloidFree :: Storabloid a => a ⊸ ()
storabloidFree x = case load x of
  Bang _ -> ()

data List a where
  Nil :: List a
  Cons :: a -> List a -> List a -- mentally substitute ⊸ for -> as GHC disallows it.

filterLinear :: (a ⊸ Maybe a) -> List a ⊸ List a
filterLinear f Nil = Nil
filterLinear f (Cons x xs) = case f x of
  Nothing -> filterLinear f xs
  Just x' -> Cons x' (filterLinear f xs)

type Queue a = List a
type Vector a = List a

newtype Bang a = Bang a

alloc   :: (Queue a ⊸ Bang a) ⊸ a
alloc k = case k Nil of
  Bang x -> x

free    :: Storabloid a => Queue a ⊸ ()
free Nil = ()
free (Cons x xs) = case storabloidFree x of
  () -> free xs

push    :: Storabloid a => a ⊸ Queue a ⊸ Queue a
push x xs = let x' = store x in seq x' (Cons x' xs)

delete  :: Storabloid a => Int -> (a ⊸ (a ⊗ Int)) ⊸ Queue a ⊸ Queue a
delete del extractId = filterLinear $
                       \x -> let (x',ident) = extractId x
                             in if del == ident
                                  then case storabloidFree x of
                                          () -> Nothing
                                  else Just x

evict   :: Storabloid a => Int -> Queue a ⊸ (Queue a, Bang (Vector a))
evict _ Nil = (Nil,Bang Nil)
evict n (Cons x xs) = case load x of
  Bang y -> case evict (n-1) xs of
    (xs', Bang ys) -> (xs', Bang (Cons y ys))

