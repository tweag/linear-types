#! /usr/bin/env bash

set -xe

# Build the executable
stack bench --no-run-benchmarks

# Find the executable, and assume it runs OUTSIDE docker:
EXE=`stack exec -- which bench-cursor`
CRIT="./bin/criterion-interactive"

set +x

echo "Using binary: $EXE"

for name in sumtree maptree;
do
  for (( depth=1; depth <= 20; depth++ ))
  do
    echo
    echo "Benchmarking tree depth $depth"
    echo "=============================="
    for variant in boxed packed ST-packed unpack-repack;
    do
        echo "Variant: $variant"
        echo "-----------------"
        set -x
        $CRIT $EXE $name $variant $depth -- -o report_${variant}_${depth}.html
        set +x
    done;
  done;
done;
