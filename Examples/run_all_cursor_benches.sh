#! /usr/bin/env bash

set -xe

# Build the executable
stack bench --no-run-benchmarks

# Find the executable, and assume it runs OUTSIDE docker:
EXE=`stack exec -- which bench-cursor`
CRIT="./bin/criterion-interactive"
set +x

echo "Using binary: $EXE"

RUNDIR=run_`hostname -s`_`date +"%s"`

function go() {
  echo "Running benchmarks with output to dir: $RUNDIR"
    
  for name in sumtree maptree;
  do
    for (( depth=1; depth <= 24; depth++ ))
    do
      echo
      echo "Benchmarking tree depth $depth"
      echo "=============================="
      for variant in boxed packed ST-packed unpack-repack;
      do
          echo "Variant: $variant"
          echo "-----------------"
          echo "START_BENCHMARK"
          echo "PROGNAME: $name"
          echo "VARIANT: $variant"
          echo "ARGS: $depth"
          set -x
          $CRIT $EXE $name $variant $depth -- \
                -o     $RUNDIR/report_${variant}_${depth}.html \
                --json $RUNDIR/report_${variant}_${depth}.json \
                --csv  $RUNDIR/report_${variant}_${depth}.csv
          set +x
          echo "END_BENCHMARK"
          echo
      done;
    done;
  done;
}

mkdir -p $RUNDIR    
go 2> /dev/stdout | tee $RUNDIR/full_benchmark_log.txt
