{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
-- import Data.Array.IO as IO
-- import Data.Array.IO as IO
-- import System.IO.Unsafe
import Data.Array.ST as ST
import Control.Monad.ST
import Data.Array

type a ⊸ b = a -> b

newtype MA a = MA (forall r s. (STArray s Int a ⊸ ST s r) -> ST s r)
data Unrestricted a where
  Unrestricted :: a -> Unrestricted a

newArray :: Int -> a -> MA a
newArray n x = MA $ \k -> do
  ar <- ST.newArray (0,n) x
  k ar

freeze :: MA a ⊸ Array Int a
freeze (MA k) = runSTArray (k return)

-- What happens when freeze is called from an unrestricted context?
-- It does not matter if "MA k" is "duplicated", because the
-- continuation k is called a single time anyway.

write :: MA a ⊸ ((Int, a) -> MA a)
write (MA k) (ix,a) = MA $ \r -> k $ \ar -> do
  ST.writeArray ar ix a
  r ar



-- Local Variables:
-- dante-project-root: "."
-- End:
