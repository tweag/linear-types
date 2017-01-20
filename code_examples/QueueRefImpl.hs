{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE LambdaCase #-}

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
  Bang _ -> () -- via GC allocation; obviously there is a more direct path

instance Storabloid Bool where
  store True = True -- This thunk will go on the linear heap (if called from a linear context)
  store False = False
  load x = case x of -- deallocation happens here.
             True -> Bang True -- in GC mode
             False -> Bang False

data List a where
  Nil :: List a
  Cons :: a -> List a -> List a -- mentally substitute ⊸ for -> as GHC disallows it.

instance Storabloid a => Storabloid (List a) where
  store Nil = Nil
  store (Cons x xs) = let !x' = store x
                          !xs' = store xs
                      in Cons x' xs'
  load = \case
    Nil -> Bang Nil
    Cons x xs -> case load x of
      Bang x' -> case load xs of
        Bang xs' -> Bang (Cons x' xs')



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

