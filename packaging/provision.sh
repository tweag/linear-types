#!/usr/bin/env bash

# install GHC, stack, etc…
echo 'deb http://ppa.launchpad.net/hvr/ghc/ubuntu trusty main' > /etc/apt/sources.list.d/ghc.list
apt-key adv --keyserver keyserver.ubuntu.com --recv-keys F6F88286
apt-get update
apt-get install -y --no-install-recommends cabal-install-2.0 ghc-8.2.1 happy-1.19.5 alex-3.1.7 \
        zlib1g-dev libtinfo-dev libsqlite3-0 libsqlite3-dev ca-certificates g++ git curl
curl -fSL https://github.com/commercialhaskell/stack/releases/download/v1.5.1/stack-1.5.1-linux-x86_64-static.tar.gz -o stack.tar.gz
curl -fSL https://github.com/commercialhaskell/stack/releases/download/v1.5.1/stack-1.5.1-linux-x86_64-static.tar.gz.asc -o stack.tar.gz.asc
apt-get purge -y --auto-remove curl
export GNUPGHOME="$(mktemp -d)"
gpg --keyserver ha.pool.sks-keyservers.net --recv-keys C5705533DA4F78D8664B5DC0575159689BEFB442
gpg --batch --verify stack.tar.gz.asc stack.tar.gz
tar -xf stack.tar.gz -C /usr/local/bin --strip-components=1
/usr/local/bin/stack config set system-ghc --global true
rm -rf "$GNUPGHOME" stack.tar.gz.asc stack.tar.gz

# Setting up the PATH
touch /home/ubuntu/.bashrc && chown ubuntu:ubuntu /home/ubuntu/.bashrc
echo 'PATH=/root/.cabal/bin:/root/.local/bin:/opt/cabal/2.0/bin:/opt/ghc/8.2.1/bin:/opt/happy/1.19.5/bin:/opt/alex/3.1.7/bin:$PATH' > /home/ubuntu/.bashrc
. /home/ubuntu/.bashrc

# Install lubuntu
apt-get install -y --no-install-recommends lubuntu-desktop

# Compile GHC
GHCBUILD=/home/ubuntu/ghc_linear
SYSBUILDDEPS="autoconf automake make wget xz-utils libtool ncurses-dev"
SYSRUNDEPS=libgmp-dev
# Already installed: gcc g++ tar

# Clone and build, but don't store the build dir OR the extra version
# of GHC. This will be a really big single step to avoid storing
# intermediary files in the unionfs layer:

LINEAR_SHA=9cf8f718b26aeacd5b5fc95cfe583e6b78e48d2f

apt-get update -y
apt-get install -y --no-install-recommends $SYSBUILDDEPS $SYSRUNDEPS
git clone --recursive git://git.haskell.org/ghc.git $GHCBUILD
cd $GHCBUILD && git remote add tweag https://github.com/tweag/ghc.git
git fetch tweag
git checkout $LINEAR_SHA
git submodule update --init --recursive
echo "BuildFlavour = quick" > $GHCBUILD/mk/build.mk
cat $GHCBUILD/mk/build.mk.sample >> $GHCBUILD/mk/build.mk
cd $GHCBUILD && ./boot && ./configure
cd $GHCBUILD make && make install
cd $GHCBUILD && git clean -xdf && git submodule foreach --recursive "git clean -xdf"
apt-get purge -y --auto-remove cabal-install-2.0 ghc-8.2.1 happy-1.19.5 alex-3.1.7

# Checks out sources for the artifacts
ARTIFACT_REF=29a010b32f8b826fd5e21477596c2b760e8259ff
ARTIFACT_HOME=/home/ubuntu/artifact
git clone --recursive --single-branch -b artifact https://github.com/tweag/linear-types.git $ARTIFACT_HOME
cd $ARTIFACT_HOME && git checkout $ARTIFACT_REF

# Sets up permissions for repositories
chown -R ubuntu:ubuntu $GHCBUILD
chown -R ubuntu:ubuntu $ARTIFACT_HOME

# Build dependencies for benches
apt-get install -y make xz-utils gnuplot
cd $ARTIFACT_HOME && su ubuntu -c 'make STACK_ARGS="--install-ghc" bin/criterion-interactive bin/hsbencher-graph'
cd $ARTIFACT_HOME && git submodule foreach --recursive "git clean -xdf"

# Sets up permissions for repositories
chown -R ubuntu:ubuntu $GHCBUILD
chown -R ubuntu:ubuntu $ARTIFACT_HOME

# Final cleaning of apt lists to spare a little upload space
rm -rf /var/lib/apt/lists/*
