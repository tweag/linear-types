
# Inherit the benchmarks and all the tools:
FROM parfunc/linear-haskell-popl18-artifact:0.0.6

# Run the benchmarks to produce results:
RUN cd /examples && make bench

# Generate the plots via gnuplot:
RUN cd /examples/plots && make 
