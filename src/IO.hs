-- | 

{-# LANGUAGE MagicHash #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RebindableSyntax #-}

module IO where

import qualified Prelude as P
import System.IO (Handle)

------------------------------------------------------------
    
-- type World = State# RealWorld -- Unlifted.
data World = World

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
