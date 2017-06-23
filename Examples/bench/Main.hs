-- |

{-# LANGUAGE BangPatterns #-}

module Main where

import qualified ByteArray as BA
import PackedTree
-- import Linear.Common
import Linear.Unsafe

-- import Criterion
import Data.Time.Clock
import System.Environment
import Control.Exception (evaluate)
import Control.DeepSeq (force)
import System.Mem
----------------------------------------------

--    diffUTCTime

mkTree :: Int -> Tree
mkTree depth = go 0 depth
  where
   go x 0 = Leaf x
   go x n = Branch (go x (n-1))
                   (go (x+2^(n-1)) (n-1))

timePrint :: IO a -> IO a
timePrint act = do
  t1 <- getCurrentTime
  c1 <- getAllocationCounter
  x  <- act
  c2 <- getAllocationCounter
  t2 <- getCurrentTime
  putStrLn $ show (diffUTCTime t2 t1) ++", alloc "++ comma(abs(c2-c1))
  return x

comma :: (Show a,Num a) => a -> String
comma n = reverse (go (reverse (show n)))
  where go (a:b:c:d:r) = a:b:c:',': go (d:r)
        go ls        = ls
         
pureMap :: (Int -> Int) -> Tree -> Tree
pureMap f (Leaf n)     = Leaf   (f n)
pureMap f (Branch x y) = Branch (pureMap f x) (pureMap f y)
         
main :: IO () 
main = do
  putStr "Fill 10K bytes in a ByteArray: "
  _ <- timePrint $ evaluate $ 
         BA.alloc 20000 (unsafeCastLinear
                         (\c -> let go 0 = c
                                    go n = BA.writeByte 33 (go (n-1))
                                in BA.freeze (go (10000::Int))))

  [dep] <- getArgs
  putStr "\nGenerate tree: "
  tr <- timePrint $ evaluate $ force $ mkTree (read dep)
  putStr "Boxed map: "
  !_ <- timePrint $ evaluate $ force $ pureMap (+1) tr

  putStr "Pack tree: "
  tr' <- timePrint $ evaluate $ force $ packTree tr
  performGC

  putStr "de/re-serialize and map: "
  !_ <- timePrint $ evaluate $ force $ packTree $ pureMap (+1) $ unpackTree tr'
  performGC
  
  putStr "Unboxed map: "
  !_ <- timePrint $ evaluate $ force $ mapTree (+1) tr'
  performGC

  return ()
