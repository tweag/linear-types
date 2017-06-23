-- |

{-# LANGUAGE BangPatterns #-}

module Main where

import PackedTree
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
  x  <- act
  t2 <- getCurrentTime
  putStrLn (show (diffUTCTime t2 t1))
  return x

pureMap :: (Int -> Int) -> Tree -> Tree
pureMap f (Leaf n)     = Leaf   (f n)
pureMap f (Branch x y) = Branch (pureMap f x) (pureMap f y)
         
main :: IO () 
main = do
  [dep] <- getArgs
  putStr "Generate tree: "
  tr <- timePrint $ evaluate $ force $ mkTree (read dep)
  putStr "Boxed map: "
  !_ <- timePrint $ evaluate $ force $ pureMap (+1) tr

  putStr "Pack tree: "
  tr' <- timePrint $ evaluate $ force $ packTree tr
  performGC

  putStr "Unboxed map: "
  !_ <- timePrint $ evaluate $ force $ mapTree (+1) tr'
  performGC
  putStr "de/re-serialize and map: "
  !_ <- timePrint $ evaluate $ force $ packTree $ pureMap (+1) $ unpackTree tr'

  return ()
