

# The image for the examples/benchmarks
VER=0.0.9
BASETAG=parfunc/linear-haskell-popl18-artifact
TAG=$(BASETAG):$(VER)

# The underlying image for the extended, linear GHC:
GHCTAG=popl18
GHCREPO=tweag/linear-types:$(GHCTAG)

all: build test docs

# By default use the Dockerized versions:
build: build1
test:  test1

# Commands for running from *outside* the container:
#===============================================================================
# Here are two ways to build the examples and benchmarks.

# Option (1): Build the benchmark container as a second docker image:
build1: image
image: fetch
#	(git clean -fxd || echo ok)
	docker build -t $(TAG) -t $(BASETAG):latest . 
# Fetch the upstream image.
fetch:
	docker pull $(GHCREPO)

push:
	docker push $(TAG)

shell:
	docker run -it $(TAG) bash

# Test with both pure and mutable cursor implementations:
test1:
	docker run -it $(TAG) make STACK_ARGS="--no-docker" test2

# --------------------

# Option (2): instead use stack and only GHC comes from a docker image.
build2:
# Don't run the tests and benchmarks on "build":
	stack docker pull
	stack --docker build
	stack --docker test --no-run-tests

# Test with both pure and mutable cursor implementations:
test2:
	stack $(STACK_ARGS) test --flag Examples:-pure
#	stack $(STACK_ARGS) test --flag Examples:pure


# Targets for use inside or outside the container:
#===============================================================================

./bin/criterion-interactive: 
	cd ./deps; stack $(STACK_ARGS) install criterion-external

./bin/hsbencher-graph: 
	cd ./deps; stack $(STACK_ARGS) install hsbencher hsbencher-graph

docs: Artifact_HOWTO_Guide.html
Artifact_HOWTO_Guide.html: README.md
#	which pandoc || stack --resolver=lts-8.6 install pandoc
	pandoc $^ -o $@

# Run the benchmarks and tests (inside or outside a container)
#===============================================================================

# Just an example of ONE benchmark you might run:
# Assumes you have run "build1" or "build2".
# In the former case, this had better be invoked from INSIDE the Docker container.
example_bench: ./bin/criterion-interactive 
	./bin/criterion-interactive stack exec -- bench-cursor sumtree packed 5 -- -o report.h

# A full run of the Cursors benchmark suite:
run-bench:
	./run_all_cursor_benches.sh

clean:
	rm -rf bin/*
	stack clean || echo ok
	cd deps; stack clean || echo ok

.PHONY: all example_bench run-bench clean build1 build2 test1 test2
