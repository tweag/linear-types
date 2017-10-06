FROM tweag/linear-types:popl18

RUN apt-get install -y make xz-utils

WORKDIR /examples

ADD ./stack.yaml      /examples/stack.yaml
ADD ./Examples.cabal  /examples/Examples.cabal
ADD ./bench           /examples/bench
ADD ./test            /examples/test
ADD ./src             /examples/src

RUN cd /examples && stack --no-docker build
RUN cd /examples && stack --no-docker test  --no-run-tests 

# Install GHC 8.0 to build these dependencies (executables):
RUN cd /tmp && stack --resolver=lts-8.6 --no-docker setup --no-system-ghc
# RUN cd deps/hsbencher && stack --no-docker setup --install-ghc
ADD ./deps/stack.yaml         /examples/deps/stack.yaml
ADD ./deps/criterion-external /examples/deps/criterion-external
ADD ./Makefile                /examples/Makefile
RUN make STACK_ARGS="--no-docker --no-system-ghc" bin/criterion-interactive 
RUN make STACK_ARGS="--no-docker --no-system-ghc" bin/hsbencher-graph
# If we combined all steps that need GHC 8.0, we could clean up like this:
#   rm -rf ~/.stack/snapshots/x86_64-linux/lts-8.6/ && \
#   rm -rf ~/.stack/programs/x86_64-linux/ghc-8.0.2

# Attempt to build with (linear) GHC 8.2.  vector-algorithms dependency fails to build:
# RUN make STACK_ARGS="--skip-ghc-check --resolver=nightly-2017-10-06" bin/criterion-interactive
