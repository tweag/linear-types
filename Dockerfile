# This is used to build an image "tweag/linear-types" on dockerhub
# ----------------------------------------------------------------
#
# CHANGES
# v1.0.3
# ------
#
# - Even more bug fixes
#
# v1.0.2
# ------
#
# - Many, many bug fixes
#
# v1.0.1
# ------
#
# - Many bug fixes
# - Constructors have one multiplicity variable per argument
#
# v1.0.0
# -------
#
# - Based on the submission https://phabricator.haskell.org/D5401 (first iteration)
# - Which is based on a v8.7 from 2018-11-30
# - Many bug fixes
#
# v0.1.11
# -------
#
# - Fix broken installation in v0.1.10
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
FROM haskell:8.6.5
# Commit hash of GHC+linear-types in the repository github.com/tweag/ghc
ENV LINEAR_SHA 0971e23ea379ad311666c0da777012e7a09c92d1

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
    stack install happy && \
    git clone --recursive https://gitlab.haskell.org/ghc/ghc.git $GHCBUILD && \
    cd $GHCBUILD && git remote add tweag https://github.com/tweag/ghc.git && \
    git fetch tweag && \
    git checkout $LINEAR_SHA && \
    git submodule sync && \
    git submodule update --init --recursive && \
    echo "BuildFlavour = quick" > $GHCBUILD/mk/build.mk && \
    cat $GHCBUILD/mk/build.mk.sample >> $GHCBUILD/mk/build.mk && \
    cd $GHCBUILD && ./boot && ./configure && \
    make -j6 && make install && \
    echo "== Remove GHC sources ==" && \
    rm -rf $GHCBUILD && \
    echo "== Remove /opt GHC installation ==" && \
    rm -rfv /opt/ghc && rm -rfv /opt/cabal && \
    echo "== Cleanup apt packages ==" && \
    apt-get purge -y --auto-remove cabal-install ghc $SYSBUILDDEPS # && \
    rm -rf /var/lib/apt/lists/*
