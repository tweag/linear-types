-- | 

{-# LANGUAGE MagicHash #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}

module IO where

import qualified Prelude as P
import System.IO (Handle)
import System.IO.Unsafe (unsafePerformIO)
import GHC.Prim

------------------------------------------------------------
    
-- type World = State# RealWorld -- Unlifted.
data World = World

data Tensor a b where
    Tensor :: a ⊸ b ⊸ Tensor a b
    
-- newtype IO' l a = IO' (World ⊸ Tensor World (R l a))
newtype IO' l a = IO' (World ⊸ (World, R l a))

-- | Cannot use lowercase ω as a type constructor...
data Weight = One | Ω 
    
-- | Result type.  This needs a subscripted arrow, which we don't have
-- yet in the prototype.
data R (l::Weight) a where
    R1 :: a ⊸  R 'One a
    RN :: a -> R 'Ω   a

-- | Again, we lack a subscripted, multiplicity-polymorphic arrow, so
-- this is an approximation.
data Arrow l a b where
  LA :: (a ⊸ b)  -> Arrow 'One a b
  UA :: (a -> b) -> Arrow 'Ω   a b
          
-- type Arrow (l::Weight) a b = ()
          
(>>=) :: IO' l a ⊸ (Arrow l a (IO' l' b)) -> IO' l' b
(>>=) = P.undefined

returnL :: a ⊸ IO' 'One a
returnL = P.undefined

return :: a -> IO' 'Ω a
return = P.undefined
          
---------------------
        
open :: P.String -> IO' One Handle
open = P.undefined

close :: Handle ⊸ IO' l ()
close = P.undefined

---------------------

t1 :: IO' l ()
t1 = open "test.txt" >>= LA (\h -> close h)

t2 :: IO' 'Ω ()
t2 = open "test.txt" >>= LA (\h -> close h >>= UA (\() -> return ()))

t3 :: IO' 'One ()
t3 = open "test.txt" >>= LA (\h -> close h >>= UA (\() -> returnL ()))

-- But how do we do some work inbetween?
delayedClose :: Handle ⊸ IO' Ω ()
delayedClose h = close h -- FIXME:
-- This fails, giving 'h' weight ω!:
-- delayedClose h = return () >>= LA (\() -> close h)

t4 :: IO' 'Ω ()
t4 = open "test.txt" >>= LA delayedClose
