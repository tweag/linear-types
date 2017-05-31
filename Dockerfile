
# This is used to build an image "parfunc/linear-ghc" on dockerhub
# ----------------------------------------------------------------

# 17.04 has GHC 8.0.2
# FROM ubuntu:17.04

FROM ubuntu:16.04

RUN apt update -y && \
    apt-get install -y git autoconf happy alex make wget tar xz-utils

RUN apt-get install -y gcc

# Unfortunately the system GHC install would be 8.0.2, which doesn't
# work with the linear-types branch at the moment [2017.05.31].
#
# RUN apt-get install -y ghc && ghc --version


# This will be a really big single step to avoid storing the bootstrap
# version of GHC in the unionfs layer:
# --------------------------------------------------------------------
RUN mkdir /ghctmp && cd /ghctmp && \
    wget https://downloads.haskell.org/~ghc/8.0.1/ghc-8.0.1-x86_64-deb8-linux.tar.xz && \
    tar xf ghc-8.0.1-x86_64-deb8-linux.tar.xz && \ 
    cd ghc-8.0.1 && ./configure --prefix=/ghctmp && make install

RUN git clone --recursive git://git.haskell.org/ghc.git /ghc

# Check out branch "linear-types"
RUN cd /ghc && git remote add tweag https://github.com/tweag/ghc.git && \
    git fetch --all && \
    git checkout 36666a9db79adeb27dffebbfb5dbe2939d0f0972

RUN export PATH=/ghctmp/bin:$PATH && \
    cd /ghc && ./boot && ./configure

RUN export PATH=/ghctmp/bin:$PATH && \
    cd /ghc make -j4 && make install

# TODO:
#    rm -rf /ghctmp /ghc
# --------------------------------------------------------------------
