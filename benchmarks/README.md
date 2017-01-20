# Linear type benchmarks for a simple queue

## Objective

The objective of these benchmarks is to see how GC collections affect the
performance of haskell, in particular the problem we are interested in is the latency
introduced by GC collection.

The test here is to push data on queue (implemented as a linked list in order to make
allocation as common as possible) and measure the latency. The baseline used in this test is
a C implementation (in the `c` folder).

## Requirements

For this microbenchmark you will need hyperion. 
The current build operations are to be improved, and are the following.

* clone hyperion at teh same level as the linear types folder
* modify the batching strategy of hyperion, 
```
-    foldMap (runBenchmark (sample 100 (fixed 5))) bks
+    foldMap (runBenchmark (sample 1000000 (fixed 1))) bks
```
* install python, matplotlib and numpy (used by `analysis.py`)
* stack locally installed

## Use

You can simply run `sh run_benchmarks.sh` which should output a pyplot graph
of the latency for the quantiles 90, 96, 99, 99.6 .. 99.9999 (done on 1.000.000 data points)

The C code is called by an FFI (`haskell/src/CQueue.hs`). 
The haskell code is in `haskell/src/Queue.hs`. 

The operations beeing benchmarked are push and pops on a 10.000 nodes long queue.

## Results

We can see that in the lower quantiles, the haskell implementation  is faster than the C one,
probably due to the FFI cost. 
On the other hand in the higher quantiles we can see that haskell's latency grows extremely
fast, up untill it is almost two orders of magnitude slower than the C FFi.
