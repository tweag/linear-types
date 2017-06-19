
# This is used to build an image "parfunc/linear-ghc" on dockerhub
# ----------------------------------------------------------------

# 17.04 has GHC 8.0.2
# FROM ubuntu:17.04

# 16.04 has GHC 7.10.3:
FROM ubuntu:16.04

RUN apt-get update -y && \
    apt-get install -y git autoconf automake make wget tar xz-utils \
      gcc g++ libgmp-dev libtool ncurses-dev g++
# python bzip2 ca-certificates \int

# This will be a really big single step to avoid storing the bootstrap
# version of GHC in the unionfs layer:
# --------------------------------------------------------------------
# Option 1: Manual install of GHC:
# ---------
# RUN mkdir /tmp/ghc && cd /tmp/ghc && \
#     wget https://downloads.haskell.org/~ghc/8.0.1/ghc-8.0.1-x86_64-deb8-linux.tar.xz && \
#     tar xf ghc-8.0.1-x86_64-deb8-linux.tar.xz && \ 
#     cd ghc-8.0.1 && ./configure --prefix=/tmp/ghc && make install
# ENV GHCBOOTSTRAP /tmp/ghc/bin

# Option 2: System install of GHC:
# ---------
# Unfortunately the system GHC install would be 8.0.2, which doesn't
# work with the linear-types branch at the moment [2017.05.31].
#
# RUN apt-get install -y ghc happy alex && ghc --version


# Option 3: Stack install of GHC.  LTS 7.24 is GHC 8.0.1
# ---------
# ENV RESOLVER lts-7.24
# Newer gives us GHC 8.0.2:
ENV RESOLVER lts-8.18

#RUN apt-get install -y haskell-stack && \
#    stack --version
# This is the latest version:
# ENV STACKURL https://www.stackage.org/stack/linux-x86_64-static
# This is a stable/immutable link:
ENV STACKURL https://github.com/commercialhaskell/stack/releases/download/v1.4.0/stack-1.4.0-linux-x86_64-static.tar.gz
RUN cd /tmp/ && \
    wget --progress=dot:giga --no-clobber --no-check-certificate $STACKURL && \
    tar xzvf stack-1.4.0-linux-x86_64-static.tar.gz && mv stack-*-linux-x86_64-static/stack /usr/bin/

# Happy problems without these:
ENV LANG     C.UTF-8
ENV LC_ALL   C.UTF-8
ENV LANGUAGE C.UTF-8

ENV GHCBOOTSTRAP /root/.stack/programs/x86_64-linux/ghc-8.0.2/bin
ENV GHCBUILD /tmp/ghc_linear

# Bootstrapped with ghc 8.0.1:
# ENV LINEAR_SHA 36666a9db79adeb27dffebbfb5dbe2939d0f0972
# Bootstrapped with ghc 8.0.2, rebased with some new stuff:
ENV LINEAR_SHA 188a72043b94cd16c3e00bb6da801c008f374fc4

# Clone and build, but don't store the build dir OR the extra version of GHC.
RUN stack --version && stack --install-ghc --resolver=$RESOLVER --local-bin-path=/usr/bin/ install happy alex && \
    git clone --recursive git://git.haskell.org/ghc.git $GHCBUILD && \
    cd $GHCBUILD && git remote add tweag https://github.com/tweag/ghc.git && \
    git fetch --all && \
    git checkout $LINEAR_SHA && \
    git submodule update --init --recursive && \
    echo "BuildFlavour = quick" > $GHCBUILD/mk/build.mk && \
    cat $GHCBUILD/mk/build.mk.sample >> $GHCBUILD/mk/build.mk && \
    export PATH=$GHCBOOTSTRAP:$PATH && \
    cd $GHCBUILD && ./boot && ./configure && \
    cd $GHCBUILD make -j4 && make install && \
    rm -rf $GHCBUILD /root/.stack/programs/x86_64-linux/ghc-8.0.*
# --------------------------------------------------------------------
