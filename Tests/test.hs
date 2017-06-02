{-# LANGUAGE LambdaCase, GADTs #-}
-- run with $ ./inplace/bin/ghc-stage1 test.hs

module Test where

-- Bindings whose name starts with "incorrect" must fail, the rest shouldn't

myid :: a ⊸ a
myid x = x

-- Must fail:
incorrectDup :: a ⊸ (a,a)
incorrectDup x = (x,x)

-- Must fail:
incorrectDrop :: a ⊸ ()
incorrectDrop x = ()

dup :: a -> (a,a)
dup x = (x,x)

incorrectApp1 :: a ⊸ ((a,Int),(a,Int))
incorrectApp1 x = dup (x,0)

incorrectApp2 :: (a->b) -> a ⊸ b
incorrectApp2 f x = f x

incorrectIf :: Bool -> Int ⊸ Int
incorrectIf x n =
  if x then n else 0

correctIf :: Bool -> a ⊸ a
correctIf x n =
  if x then n else n

incorrectCase :: Bool -> Int ⊸ Int
incorrectCase x n =
  case x of
    True -> n
    False -> 0

correctCase :: Bool -> a ⊸ a
correctCase x n =
  case x of
    True -> n
    False -> n

incorrectEqn :: Bool -> Int ⊸ Int
incorrectEqn True  n = n
incorrectEqn False n = 0

correctEqn :: Bool -> Int ⊸ Int
correctEqn True  n = n
correctEqn False n = n

incorrectLCase :: Int ⊸ Bool -> Int
incorrectLCase n = \case
  True -> n
  False -> 0

correctLCase :: Int ⊸ Bool -> Int
correctLCase n = \case
  True -> n
  False -> n

fst :: (a,b) -> a
fst (a,_) = a

incorrectFst :: (a,b) ⊸ a
incorrectFst (a,_) = a

incorrectFstVar :: (a,b) ⊸ a
incorrectFstVar (a,b) = a

incorrectFirstDup :: (a,b) ⊸ ((a,a),b)
incorrectFirstDup (a,b) = ((a,a),b)

incorrectFstFst :: ((a,b),c) ⊸ a
incorrectFstFst ((a,_),_) = a

data Test a
  = Foo a a
  | Bar a

incorrectTestFst :: Test a ⊸ a
incorrectTestFst (Foo a _) = a
incorrectTestFst (Bar a)   = a

data Unrestricted a where Unrestricted :: a -> Unrestricted a

unrestrictedDup :: Unrestricted a ⊸ (a, a)
unrestrictedDup (Unrestricted a) = (a,a)

incorrectUnrestricted :: a ⊸ Unrestricted a
incorrectUnrestricted a = Unrestricted a

data NotUnrestricted a where NotUnrestricted :: a ⊸ NotUnrestricted a

incorrectUnrestrictedDup :: NotUnrestricted a ⊸ (a,a)
incorrectUnrestrictedDup (NotUnrestricted a) = (a,a)

newtype Unrestricted2 a where Unrestricted2 :: a -> Unrestricted2 a

unrestricted2Dup :: Unrestricted2 a ⊸ (a,a)
unrestricted2Dup (Unrestricted2 a) = (a,a)

type N a = a ⊸ ()

consume :: a ⊸ N a ⊸ ()
consume x k = k x

data N' a where N :: N a ⊸ N' a

consume' :: a ⊸ N' a ⊸ ()
consume' x (N k) = k x

data W = W (W ⊸ ())

wPlusTwo n = W (\(W k) -> k n)

data Nat = S Nat

natPlusOne :: Nat ⊸ Nat
natPlusOne n = S n

data D = D ()

mkD :: () ⊸ D
mkD x = D x

data Odd = E Even
data Even = O Odd

evenPlusOne :: Even ⊸ Odd
evenPlusOne e = E e

incorrectLet :: a ⊸ ()
incorrectLet a = let x = a in ()

incorrectLazyMatch :: (a,b) ⊸ b
incorrectLazyMatch x = let (a,b) = x in b

incorrectCasePromotion :: (a,b) ⊸ b
incorrectCasePromotion x = case x of (a,b) -> b

-- Inference-related behaviour. Slightly sub-optimal still.

bind1 :: (d ⊸ (a ⊸ b) ⊸ c) ⊸ d ⊸ (a⊸b) ⊸ c
bind1 b x f = b x (\a -> f a)

newtype I a = I a

bind2 :: (d ⊸ (a ⊸ b) ⊸ c) ⊸ d ⊸ (I a⊸b) ⊸ c
bind2 b x f = b x (\a -> f (I a))

bind3 :: (d ⊸ I (a ⊸ b) ⊸ c) ⊸ d ⊸ (a⊸b) ⊸ c
bind3 b x f = b x (I (\a -> f a))

bind4 :: (d ⊸ I ((a ⊸ a') ⊸ b) ⊸ c) ⊸ d ⊸ ((a⊸a')⊸b) ⊸ c
bind4 b x f = b x (I (\g -> f g))

bind5 :: (d ⊸ ((a ⊸ a') ⊸ b) ⊸ c) ⊸ d ⊸ ((a⊸a')⊸b) ⊸ c
bind5 b x f = b x (\g -> f (\a -> g a))

bind6 :: (d ⊸ I ((a ⊸ a') ⊸ b) ⊸ c) ⊸ d ⊸ ((a⊸a')⊸b) ⊸ c
bind6 b x f = b x (I (\g -> f (\a -> g a)))
