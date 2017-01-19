#!/usr/bin/env stack
-- stack --no-nix-pure runghc
--
module Main where

import Queue
import CQueue
import Hyperion.Benchmark
import Hyperion.Main

data Operation = Push | Pop
  deriving (Show, Eq)

data COperation = CPush | CPop
  deriving (Show, Eq)

benchmarks :: [Benchmark]
benchmarks = concat
  [
    generate_benchmarks Pop [0, 10..100] [1..10]
    , generate_benchmarks Push [0, 10..100] [1..10]
    , c_generate_benchmarks CPop [0, 10..100] [1..10]
    , c_generate_benchmarks CPush [0, 10..100] [1..10]
  ]

main = defaultMain benchmarks

-- Haskell utils for the tests.
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

-- Haskell utils for the tests C binding.
c_pop_n :: QueuePtr -> Int -> IO()
c_pop_n queue 0 = return ()
c_pop_n queue n = do
  _ <- c_pop queue
  c_pop_n queue (n-1)

c_push_n :: QueuePtr -> Int -> IO()
c_push_n queue 0 = return ()
c_push_n queue n = do
  c_push queue n
  c_push_n queue (n-1)

c_push_and_create :: Int -> IO QueuePtr
c_push_and_create n = do
  queue <- c_create_queue
  c_push_n queue n
  return queue

c_queue_operation :: COperation -> (QueuePtr -> Int -> IO ())
c_queue_operation CPop = c_pop_n
c_queue_operation CPush = c_push_n

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

c_generate_benchmarks :: COperation -> [Int] -> [Int] -> [Benchmark]
c_generate_benchmarks operation queue_sizes number_op = concat $
  map
    (\n ->
      (map
        (\queue_size ->
          (env
            (c_push_and_create queue_size)
            c_clear_queue
            (\queue ->
               bench
                ((show operation) ++ "_c_" ++ (show n) ++ "_on_" ++ (show queue_size))
                (use queue >>= (\x -> nfIO ((c_queue_operation operation) x n)))
            )
          )
        )
        queue_sizes
      )
    )
    number_op
