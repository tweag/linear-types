{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
import Data.Array.IO as IO
import System.IO.Unsafe
import Control.Monad.ST
import Data.Array

type a ⊸ b = a -> b

newtype MA a = MA (forall r. (IOArray Int a ⊸ IO r) -> IO r)
data Unrestricted a where
  Unrestricted :: a -> Unrestricted a

newArray :: Int -> a -> MA a
newArray n x = MA $ \k -> do
  ar <- IO.newArray (0,n) x
  k ar

freeze :: MA a ⊸ (Int -> a)
freeze (MA k) ix = unsafePerformIO $ k $ \a -> readArray a ix

-- What happens when freeze is called from an unrestricted context?
-- It does not matter if "MA k" is "duplicated", because the
-- continuation k is called a single time anyway.

write :: MA a ⊸ ((Int, a) -> MA a)
write (MA k) (ix,a) = MA $ \r -> k $ \ar -> do
  IO.writeArray ar ix a
  r ar

read :: MA a ⊸ (Int -> (MA a, Unrestricted a))
read (MA k) ix = unsafePerformIO $ k $ \a -> do
  x <- readArray a ix
  return (MA $ \k' -> k' a,Unrestricted x)

-- Local Variables:
-- dante-project-root: "."
-- End:
