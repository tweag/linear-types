# This is used to build an image "tweag/linear-types" on dockerhub
# ----------------------------------------------------------------
#
# CHANGES
#
# v0.1.10
# -------
#
# - Merge with recent v8.7 (2018-11-08)
# - Using linear types requires -XLinearTypes
# - Stabilise Core's handling of linear types
# - Fix unboxed tuples and sums
# - Without -XLinearTypes, GADTs with regular arrows are linear
# - Pattern synonyms in linear positions will raise an error
# - View patterns in linear positions will raise an error
# - Lazy patterns in linear positions will raise an error
# - Fix desugaring of do-notation
# - Many minor bug fixes
#
# v0.1.9
# ------
# - More recent v8.5
# - Basic implementation of multiplicity polymorphism
# - Linear functions are no longer automatically η-expanded
# - Data constructors are multiplicity polymorphic when used as terms (fixes #33 and #34)
# - Core lint understand linear types (it is still very fragile)
# - Fix compatibility of linear-base
#
# v0.1.8
# ------
#
# - Merged with v8.5 master
# - Fix #7: `(->)` and `(⊸)` are no longer considered equal by the
#   type checker.
# - Fixing #7 introduced some regression. It is possible to write even
#   Haskell 98 code which doesn't type-check. See #33 and #34.
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
FROM haskell:8.4.3
# Commit hash of GHC+linear-types in the repository github.com/tweag/ghc
ENV LINEAR_SHA 16ac2b7d4e7af3b33342f82e6ecb7754272927af

# Happy problems without these:
ENV LANG     C.UTF-8
ENV LC_ALL   C.UTF-8
ENV LANGUAGE C.UTF-8

ENV GHCBUILD /tmp/ghc_linear
ENV SYSBUILDDEPS  autoconf automake wget libtool ncurses-dev python3 happy alex
ENV SYSRUNDEPS  libgmp-dev xz-utils make
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
    git submodule sync && \
    git submodule update --init --recursive && \
    echo "BuildFlavour = quick" > $GHCBUILD/mk/build.mk && \
    cat $GHCBUILD/mk/build.mk.sample >> $GHCBUILD/mk/build.mk && \
    cd $GHCBUILD && ./boot && ./configure && \
    make -j6 && make install && \
    rm -rf $GHCBUILD && \
    apt-get purge -y --auto-remove cabal-install ghc $SYSBUILDDEPS # && \
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
