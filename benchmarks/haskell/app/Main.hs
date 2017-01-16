#!/usr/bin/env stack
-- stack --no-nix-pure runghc
--
{-# LANGUAGE OverloadedLists #-}

module Main where

import Data.Vector as Vector
import Queue
import Hyperion.Benchmark
import Hyperion.Main

benchmarks :: [Benchmark]
benchmarks =
    [
     series [1..10] $ \n ->
            bench "print" (use n >>= (\x -> (nfIO (push_and_create x))))
    ]

main = defaultMain benchmarks

push_n :: Queue -> Int -> IO()
push_n queue 0 = return ()
push_n queue n = do
    push queue n
    push_n queue (n-1)

push_and_create :: Int -> IO ()
push_and_create n = do
    queue <- createQueue
    push_n queue n
