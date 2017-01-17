#!/usr/bin/env stack
-- stack --no-nix-pure runghc
--
module Main where

import Queue
import Hyperion.Benchmark
import Hyperion.Main

data Operation = Push | Pop
  deriving (Show, Eq)

benchmarks :: [Benchmark]
benchmarks = concat
  [
    generate_benchmarks Pop [0, 10..100] [1..10]
    , generate_benchmarks Push [0, 10..100] [1..10]
  ]

main = defaultMain benchmarks

pop_n :: Queue -> Int -> IO()
pop_n queue 0 = return ()
pop_n queue n = do
  _ <- pop queue
  pop_n queue (n-1)

push_n :: Queue -> Int -> IO()
push_n queue 0 = return ()
push_n queue n = do
  push queue n
  push_n queue (n-1)

push_and_create :: Int -> IO Queue
push_and_create n = do
  queue <- createQueue
  push_n queue n
  return queue

queue_operation :: Operation -> (Queue -> Int -> IO ())
queue_operation Pop = pop_n
queue_operation Push = push_n

generate_benchmarks :: Operation -> [Int] -> [Int] -> [Benchmark]
generate_benchmarks operation queue_sizes number_op = concat $
  map
    (\n ->
      (map
        (\queue_size ->
          (env
            (push_and_create queue_size)
            (\_ -> return ())
            (\queue ->
               bench
                ((show operation) ++ "_" ++ (show n) ++ "_on_" ++ (show queue_size))
                (use queue >>= (\x -> nfIO ((queue_operation operation) x n)))
            )
          )
        )
        queue_sizes
      )
    )
    number_op
