-- | 

{-# LANGUAGE MagicHash #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RebindableSyntax #-}

module IO where

import qualified Prelude as P
import Prelude (Int, fromInteger, (+)) -- TODO: For testing, can be removed when everything works
import System.IO (Handle)
-- import System.IO.Unsafe (unsafePerformIO)
-- import GHC.Prim

------------------------------------------------------------
    
-- type World = State# RealWorld -- Unlifted.
data World = World

-- newtype IO' l a = IO' (World ⊸ Tensor World (R l a))
newtype IO' l a = IO' (World ⊸ (World, R l a))

unsafeIOtoIO1 :: P.IO a ⊸ IO' 'One a
unsafeIOtoIO1 = P.error "TODO: IO.unsafeIOtoIO1"

unsafeIOtoIOΩ :: P.IO a ⊸ IO' 'Ω a
unsafeIOtoIOΩ = P.error "TODO: IO.unsafeIOtoIOΩ"

-- | Cannot use lowercase ω as a type constructor...
data Weight = One | Ω 
    
-- | Result type.  This needs a subscripted arrow, which we don't have
-- yet in the prototype.
data R (l::Weight) a where
    R1 :: a ⊸  R 'One a
    RN :: a -> R 'Ω   a

-- | Again, we lack a subscripted, multiplicity-polymorphic arrow, so
-- this is an approximation.
type family Arrow l a b where
  Arrow 'One a b = a ⊸ b
  Arrow 'Ω a b = a -> b

-- type Arrow (l::Weight) a b = ()
          
(>>=) :: IO' l a ⊸ (Arrow l a (IO' l' b)) ⊸ IO' l' b
(>>=) = P.undefined

(>>) :: IO' 'Ω a ⊸ IO' l b ⊸ IO' l b
(>>) x y = x >>= \_ -> y

fail :: IO' l a
fail = P.error "IO': pattern-matching failure"

returnL :: a ⊸ IO' 'One a
returnL = P.undefined

return :: a -> IO' 'Ω a
return = P.undefined
          
---------------------
        
open :: P.String -> IO' 'One Handle
open = P.undefined

close :: Handle ⊸ IO' 'Ω ()
close = P.undefined

---------------------

t1 :: IO' 'Ω ()
t1 = open "test.txt" >>= (\h -> close h)

t2 :: IO' 'Ω ()
t2 = open "test.txt" >>= (\h -> close h >>= (\() -> return ()))

t3 :: IO' 'One ()
t3 = open "test.txt" >>= (\h -> close h >>= (\() -> returnL ()))

t3' :: IO' 'One ()
t3' = do
  h <- open "test.txt"
  () <- close h
  returnL ()

shouldFail :: IO' 'Ω Int
shouldFail = do
  x <- returnL (1::Int)
  return (x+x)

-- But how do we do some work inbetween?
delayedClose :: Handle ⊸ IO' 'Ω ()
-- delayedClose h = close h -- FIXME:
-- This fails, giving 'h' weight ω!:
delayedClose h = returnL () >>= (\() -> close h)

-- It doesn't matter whether that unit value is linear:
delayedClose' :: Handle ⊸ IO' 'Ω ()
delayedClose' h = return () >>= (\() -> close h)

t4 :: IO' 'Ω ()
t4 = open "test.txt" >>= delayedClose
