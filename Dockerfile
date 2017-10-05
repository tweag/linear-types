FROM tweag/linear-types:0.1.5

# RUN apt-get install -y valgrind gdb

ADD ./stack.yaml      /src/stack.yaml
ADD ./Examples.cabal  /src/Examples.cabal
ADD ./bench           /src/bench
ADD ./test            /src/test
ADD ./src             /src/src

RUN cd /src && stack --no-docker build
RUN cd /src && stack --no-docker test  --no-run-tests 
RUN cd /src && stack --no-docker build --no-bench
