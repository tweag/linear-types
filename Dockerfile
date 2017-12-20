# This is used to build an image "tweag/linear-types" on dockerhub
# ----------------------------------------------------------------
#
# CHANGES
#
# v0.1.7
# ------
#
# - Ship stack 1.6.1
#
# v0.1.6
# ------
#
# - Reject linear kind declarations
# - Regular syntax for linear arrow is `(->.)`. Not backwards
#   compatible! One now needs to use `-XUnicodeSytnax` in order to use
#   the `(⊸)` syntax.

# Debian+GHC+stack. See: https://hub.docker.com/_/haskell/
FROM haskell:8.2.1
# Commit hash of GHC+linear-types in the repository github.com/tweag/ghc
ENV LINEAR_SHA 8182d67f8ef1fa163bd517fff848ab6a48b625e7

# Happy problems without these:
ENV LANG     C.UTF-8
ENV LC_ALL   C.UTF-8
ENV LANGUAGE C.UTF-8

ENV GHCBUILD /tmp/ghc_linear
ENV SYSBUILDDEPS  autoconf automake make wget xz-utils libtool ncurses-dev
ENV SYSRUNDEPS  libgmp-dev
# Already installed: gcc g++ tar

# Clone and build, but don't store the build dir OR the extra version
# of GHC. This will be a really big single step to avoid storing
# intermediary files in the unionfs layer:

RUN apt-get update -y && \
    apt-get install -y --no-install-recommends $SYSBUILDDEPS $SYSRUNDEPS && \
    git clone --recursive git://git.haskell.org/ghc.git $GHCBUILD && \
    cd $GHCBUILD && git remote add tweag https://github.com/tweag/ghc.git && \
    git fetch tweag && \
    git checkout $LINEAR_SHA && \
    git submodule update --init --recursive && \
    echo "BuildFlavour = quick" > $GHCBUILD/mk/build.mk && \
    cat $GHCBUILD/mk/build.mk.sample >> $GHCBUILD/mk/build.mk && \
    cd $GHCBUILD && ./boot && ./configure && \
    cd $GHCBUILD make -j6 && make install && \
    rm -rf $GHCBUILD && \
    apt-get purge -y --auto-remove cabal-install-2.0 ghc-8.2.1 happy-1.19.5 alex-3.1.7 $SYSBUILDDEPS # && \
    rm -rf /var/lib/apt/lists/*

# XXX: the next layer is a temporary workaround waiting for upstream
# images to ship in haskell images: see
# https://github.com/freebroccolo/docker-haskell/issues/65 )
RUN apt-get update && \
    apt-get install -y --no-install-recommends curl && \
    rm -f /usr/local/bin/stack && \
    curl -fSL https://github.com/commercialhaskell/stack/releases/download/v1.6.1/stack-1.6.1-linux-x86_64-static.tar.gz -o stack.tar.gz && \
    tar -xf stack.tar.gz -C /usr/local/bin --strip-components=1 && \
    /usr/local/bin/stack config set system-ghc --global true && \
    apt-get purge -y --auto-remove curl && \
    rm -rf  /var/lib/apt/lists/* /stack.tar.gz
