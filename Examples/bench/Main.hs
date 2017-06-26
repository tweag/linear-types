-- |

{-# LANGUAGE BangPatterns #-}

module Main where

import qualified Data.ByteString as BS
import qualified ByteArray as BA
import PackedTree
-- import Linear.Common
import Linear.Std (getUnrestricted)
import Linear.Unsafe

-- import Criterion
import Data.Word
import Data.Time.Clock
import System.Environment
import Control.Exception (evaluate)
import Control.DeepSeq (force)
import Foreign.Storable (sizeOf)
import System.Mem
import System.IO (stdout, hFlush)
import GHC.Stats
----------------------------------------------

timePrint :: IO a -> IO a
timePrint act = do
  performGC
  t1 <- getCurrentTime
  s1 <- getGCStats
  c1 <- getAllocationCounter
  x  <- act
  c2 <- getAllocationCounter
  s2 <- getGCStats        
  t2 <- getCurrentTime
  putStrLn $ show (diffUTCTime t2 t1)
             ++", alloc "++ comma(bytesAllocated s2 - bytesAllocated s1)
             ++" or "++ comma(abs(c2-c1))
--  putStrLn $ "Before: "++show s1
--  putStrLn $ "After: "++show s2++"\n"
  return x

comma :: (Show a,Num a) => a -> String
comma n = reverse (go (reverse (show n)))
  where go (a:b:c:d:r) = a:b:c:',': go (d:r)
        go ls        = ls

main :: IO ()
main = do
  bytearray
  treebench

bytearray :: IO () 
bytearray = do
  let nbytes = 10000
  putStr$ "Fill "++comma nbytes++" bytes in a ByteArray: "
  bs <- timePrint $ evaluate $ 
         BA.alloc 20000 (unsafeCastLinear
                         (\c -> let go 0 = c
                                    go n = BA.writeByte 1 (go (n-1))
                                in BA.freeze (go (nbytes::Int))))
  putStr "Sum bytes of a ByteString "
  n <- timePrint $ evaluate $
         (let go b | BS.null b = 0 :: Int
                   | otherwise = fromIntegral (BA.headStorable b :: Word8) +
                                 go (BS.drop (sizeOf (0::Word8)) b)
          in go (getUnrestricted bs))
  putStrLn $ "    (Sum was "++show n++")"
  putStr "Sum bytes of a ByteString, monadic1 "
  n' <- timePrint $ evaluate $ BA.runReadM BS.empty $ 
         (let go b !acc | BS.null b = return acc
                        | otherwise = do x <- BA.headStorableOfM b
                                         go (BS.drop (sizeOf (0::Word8)) b)
                                            (fromIntegral (x::Word8) + acc)
          in go (getUnrestricted bs) (0::Int))
  putStrLn $ "    (Sum was "++show n'++")"
  putStr "Sum bytes of a ByteString, monadic2 "
  n'' <- timePrint $ evaluate $ BA.runReadM (getUnrestricted bs) $ 
         (let go !acc = do
                b <- BA.isEndM
                if b then return acc
                 else do x <- BA.headStorableM
                         go (fromIntegral (x::Word8) + acc)
          in go (0::Int))
  putStrLn $ "    (Sum was "++show n''++")"



treebench :: IO ()
treebench = do 
  [dep] <- getArgs
  putStr "\nGenerate tree: "
  tr <- timePrint $ evaluate $ force $ mkTree (read dep)

  putStr "Boxed map: "
  _ <- timePrint $ evaluate $ force $ pureMap (+1) tr

  putStr "Sum tree (unpacked): "
  _ <- timePrint $ evaluate $ pureSum tr
         
  putStr "Pack tree: "
  tr' <- timePrint $ evaluate $ force $ packTree tr

  putStr "Sum packed tree: "; hFlush stdout
  _ <- timePrint $ evaluate $ sumTree tr'

  putStr "Unpack-then-sum"
  _ <- timePrint $ evaluate $ force $ pureSum $ unpackTree tr'

{-  
  putStr "unpack/map/repack: "
  _ <- timePrint $ evaluate $ force $ packTree $ pureMap (+1) $ unpackTree tr'

  putStr "map on packed: "
  _ <- timePrint $ evaluate $ force $ mapTree (+1) tr'
-}
  return ()


mkTree :: Int -> Tree
mkTree depth = go 0 depth
  where
   go x 0 = Leaf x
   go x n = Branch (go x (n-1))
                   (go (x+2^(n-1)) (n-1))
         
pureMap :: (Int -> Int) -> Tree -> Tree
pureMap f (Leaf n)     = Leaf   (f n)
pureMap f (Branch x y) = Branch (pureMap f x) (pureMap f y)

pureSum :: Tree -> Int
pureSum (Leaf n)     = n
pureSum (Branch x y) = pureSum x + pureSum y

         
