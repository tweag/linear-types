
# Inherit the benchmarks and all the tools:
FROM parfunc/linear-haskell-popl18-artifact:0.0.12

# ADD . /examples/plots

# Run the benchmarks to produce results:
RUN cd /examples && make STACK_ARGS="--no-docker" run-bench

# Generate the plots via gnuplot:
RUN cd /examples/plots && make 
