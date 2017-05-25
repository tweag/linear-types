
# This is used to build an image "parfunc/linear-ghc" on dockerhub

FROM ubuntu:16.04
RUN apt update -y && \
    apt-get install -y ghc
RUN apt-get install -y git

RUN git clone --recursive git://git.haskell.org/ghc.git /ghc

# Check out branch "linear-types"
RUN cd /ghc && git remote add tweag https://github.com/tweag/ghc.git && \
    git fetch --all && \
    git checkout 36666a9db79adeb27dffebbfb5dbe2939d0f0972

RUN apt-get install -y autoconf
RUN apt-get install -y happy alex
RUN apt-get install -y make

RUN cd /ghc && ./boot && ./configure && make -j4
