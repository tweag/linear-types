-- | The root of the dependence hierarchy -- the most widely used bits
-- included everywhere else.  This is reexported by Linear.Std.

{-# LANGUAGE GADTs #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE RankNTypes #-}

module Linear.Common where
import GHC.Types (Type, TYPE, RuntimeRep)
    
-- * Unrestricted

-- RRN [2017.06.27] Possible GHC Bug.  Making this a newtype causes segfaults.
-- newtype Unrestricted a where
data Unrestricted a where
    Unrestricted :: -- forall (r :: RuntimeRep) (a :: TYPE r) .
                    a -> Unrestricted a
  deriving Show
                         
{-
data Unrestricted a where
    Unrestricted :: a -> Unrestricted a
  deriving (Show,Eq)
-}

{-# INLINE getUnrestricted #-}
getUnrestricted :: Unrestricted a ⊸ a
getUnrestricted (Unrestricted x) = x

{-# INLINE mapU #-}
mapU :: (a ⊸ b) -> Unrestricted a ⊸ Unrestricted b
mapU f (Unrestricted a) = Unrestricted (f a)

{-# INLINE forceUnrestricted #-}
forceUnrestricted :: Unrestricted a ⊸ Unrestricted a
forceUnrestricted (Unrestricted a) = Unrestricted a

linerror :: forall (a :: Type) (r :: RuntimeRep) (b :: TYPE r)  .
            String -> a ⊸ b
linerror = error

-- Hard-coded constant:
--------------------------------------------------------------------------------
-- | Size allocated for each regions: 4KB.
regionSize :: Int
regionSize =
  -- 4096 -- in Bytes
  500 *1000*1000
--  5 * 1000 * 1000 * 1000

           
