-- |

{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}

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
import Control.Monad
import Control.Exception (evaluate)
import Control.DeepSeq (force)
import Foreign.Storable (sizeOf)
import System.Mem
import System.IO (stdout, stderr, hFlush, hPutStrLn, isEOF)
import System.Exit
import GHC.Stats
import qualified Cursors.ST as S
import Control.Monad.ST
----------------------------------------------

putFlushLn :: String -> IO ()
putFlushLn s = do hPutStrLn stdout s; hFlush stdout 

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
  args <- getArgs
  case args of
    [] ->  do putStrLn " Running a default benchmark set with human-readable output."
              putStrLn helpMsg
              bytearray
              treebench
    [name, variant, depth] -> runBench name variant (read depth)
    _ -> error$ "benchmark expects three command line arguments, not: "++show args
              ++ "\n\n Help:\n"++ helpMsg

helpMsg :: String
helpMsg = unlines
  [ "-----------------------------------------------"
  , " For a more systematic approach, try arguments:"
  , "  <bench-name> <variant> <tree-depth> "
  , " Where bench-name is: sumtree, maptree"
  , " And variant is: packed boxed unpack-repack ST-packed "
  , " The same tree-depth is used for all batches "
  , " of benchmark repetitions."
  , "-----------------------------------------------" ]

-- | Prevent the compiler from optimizing away the benchmark.
{-# NOINLINE ignoreMe #-}
ignoreMe :: Int -> a -> a
ignoreMe _ a = a

-- | Run a single benchmark in the request/response interactive mode.
runBench :: String -> String -> Int -> IO ()
runBench name variant dep = do
  tr  <- evaluate $ force $ mkTree dep
  putFlushLn $ "Generated a tree of depth "++show dep

  let {-# INLINE mkBenchs #-}
      mkBenchs :: (Int -> a) -> (Int -> b) -> IO ()
      mkBenchs sumBody mapBody = do 
        weAreReady
        case name of
          "sumtree" ->
              benchLoop $ \reps -> 
                 forM_ [1..reps] $ \ix ->
                   void $ evaluate (sumBody ix)
          "maptree" ->
              benchLoop $ \reps -> 
                 forM_ [1..reps] $ \ix ->
                   void $ evaluate (mapBody ix)
          _ -> error $ "Unknown benchmark name: "++name

  case variant of
    "boxed" -> do mkBenchs (\ix -> pureSum (ignoreMe ix tr))
                           (\ix -> force $ pureMap (+1) (ignoreMe ix tr))

    "packed" -> do tr' <- evaluate $ force $ packTree dep tr
                   mkBenchs (\ix -> sumTree (ignoreMe ix tr'))
                            (\ix -> mapTree dep (+1) (ignoreMe ix tr'))

    "ST-packed" -> do tr' <- timePrint $ evaluate $ packTreeST dep tr
                      mkBenchs (\ix -> sumTreeST (ignoreMe ix tr'))
                               (\ix -> mapTreeST dep (+1) (ignoreMe ix tr'))

    "unpack-repack" -> do tr' <- evaluate $ force $ packTree dep tr
                          mkBenchs (\ix -> pureSum  $ unpackTree (ignoreMe ix tr'))
                                   (\ix -> packTree dep $ pureMap (+1) $ unpackTree (ignoreMe ix tr'))

    _ -> error $ "Unrecognized 'variant': "++variant

  return ()
 where
   benchLoop fn = do mreps <- startBatch
                     case mreps of
                       Nothing   -> do hPutStrLn stderr "Benchmark shutting down cleanly..."
                                       exitSuccess
                       Just reps -> do _ <- fn reps
                                       doneBatch
                                       benchLoop fn
   weAreReady :: IO ()
   weAreReady = do performGC
                   putFlushLn "READY"
                   putFlushLn "Now waiting for START_BENCH command from harness... (or EXIT)"
   
   startBatch :: IO (Maybe Int)
   startBatch = do
                   b <- isEOF
                   if b then return Nothing
                     else do 
                      ln <- getLine
                      case words ln of                     
                        ["START_BENCH", reps] ->
                           return $ Just $ 
                             parseInt "Failed to parse repetitions as a number: " reps
                        ["EXIT"] -> return Nothing
                        oth -> error$ "Bad command from benchmark harness: "++show oth
   doneBatch = putFlushLn "END_BENCH"


parseInt :: String -> String -> Int
parseInt msg str = 
  case reads str of
    ((n,_):_) -> n
    _ -> error$ msg++" "++str
         
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
  -- [dep_] <- getArgs
  -- let dep = (parseInt "Failed to parse tree-depth number: " dep_)
  let dep = 17 
  putStr "\nGenerate tree: "
  tr <- timePrint $ evaluate $ force $ mkTree dep
        
  putStr "pack-tree: "
  tr' <- timePrint $ evaluate $ force $ packTree dep tr
  putStrLn $ "Prefix of resulting packed tree "++take 80 (show tr')

  putStr "sumtree-boxed: "
  s1 <- timePrint $ evaluate $ pureSum tr
  putStrLn $ "    (sum was "++show s1++")"
         
  putStr "sumtree-packed: "; hFlush stdout
  s2 <- timePrint $ evaluate $ sumTree tr'
  putStrLn $ "    (sum was "++show s2++")"

  putStr "unpack-then-sumtree: "
  _ <- timePrint $ evaluate $ force $ pureSum $ unpackTree tr'

  putStrLn ""
  putStr "map-boxed: "
  _ <- timePrint $ evaluate $ force $ pureMap (+1) tr

  putStr "unpack-map-repack: "
  _ <- timePrint $ evaluate $ force $ packTree dep $ pureMap (+1) $ unpackTree tr'

  putStr "map-packed: "; hFlush stdout
  _ <- timePrint $ evaluate $ force $ mapTree dep (+1) tr'

  putStrLn "\nDone with linear-cursor benchmarks.  Now running ST ones."
  putStrLn "----------------------------------------\n"

  putStr "pack-tree-ST: "
  tr'' <- timePrint $ evaluate $ packTreeST dep tr
  putStrLn $ "Prefix of resulting packed tree "++take 80 (show tr'')
  putStr "sum-tree-ST: "
  s3 <- timePrint $ evaluate $ sumTreeST tr''
  putStrLn $ "    (sum was "++show s3++")"

  putStr "map-packed-tree-ST: "
  _ <- timePrint $ evaluate $ mapTreeST dep (+1) tr''

  return ()


--------------------------------------------------------------------------------

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

packTreeST :: Depth -> Tree -> S.Packed Tree
packTreeST dep tr = S.finish (do buf <- S.allocC (treeMaxByteSize dep)
                                 go tr buf)
  where
    go :: Tree -> S.Needs s (Tree ': r) Tree -> ST s (S.Needs s r Tree)
    go (Leaf n) buf = S.writeLeaf n buf
    go (Branch x y) buf1 =
        do buf2 <- S.writeBranchTag buf1
           buf3 <- go x buf2
           go y buf3

sumTreeST :: S.Packed Tree -> Int
sumTreeST pkd = runST (fmap fst (go (S.toHas pkd)))
  where
    go :: forall s r . S.Has s (Tree ': r) -> ST s (Int, S.Has s r)
    go h = S.caseTree h 
               S.readC -- Leaf
               (\h1 -> -- Branch
                  do (x,h2) <- go h1
                     (y,h3) <- go h2
                     return $! (,h3) $! x+y)

{-# INLINE mapTreeST #-}
mapTreeST :: Depth -> (Int -> Int) -> S.Packed Tree -> S.Packed Tree 
mapTreeST dep fn pkd = S.finish
                   (do n0 <- S.allocC (treeMaxByteSize dep)
                       (_,n1) <- go (S.toHas pkd) n0
                       return n1)
 where
  go :: S.Has s (Tree ': r) -> S.Needs s (Tree ': r) t
     -> ST s ( S.Has s r, S.Needs s r t)
  go h1 n1 = S.caseTree h1
             (\h2 -> do (x,h3) <- S.readC h2
                        n2 <- S.writeLeaf (fn x) n1
                        return $! (h3,n2))
             (\h2 -> do n2 <- S.writeBranchTag n1
                        (h3,n3) <- go h2 n2
                        go h3 n3)

--------------------------------------------------------------------------------
