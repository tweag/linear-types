

# The image for the examples/benchmarks
VER=0.0.1
BASETAG=tweag/linear-haskell-popl18-artifact
TAG=$(BASETAG):$(VER)

# The base image for the extended GHC:
GHCTAG=popl18
GHCREPO=tweag/linear-types:$(GHCTAG)


all: docs

#all: ./bin/criterion-interactive
#	stack docker pull

# The Dockerfile in this directory is for debugging
#debug:
#	docker build -t debug/linear-types .
#	stack --docker-image debug/linear-types build
#	stack --docker-image debug/linear-types test --no-run-tests
#	stack --docker-image debug/linear-types exec bash

# Fetch the upstream image.
fetch:
	docker pull $(GHCREPO)

# Commands for running from outside the container:
#===============================================================================

# Option (1): Build the benchmark container as a second docker image:
build1: image
image: fetch
#	(git clean -fxd || echo ok)
	docker build -t $(TAG) -t $(BASETAG):latest . 

# Option (2): instead use stack and only GHC comes from a docker image.
# Build but don't run the tests and benchmarks.
build2:
	stack docker pull
	stack --docker build
	stack --docker test --no-run-tests
	stack --docker bench --no-bench

# For building inside or outside the container:
#===============================================================================

./bin/criterion-interactive:
	mkdir -p ./bin
	cd ./criterion-external; stack install --local-bin-path=../bin

docs: Artifact_HOWTO_Guide.html
Artifact_HOWTO_Guide.html: README.md
#	which pandoc || stack --resolver=lts-8.6 install pandoc
	pandoc $^ -o $@

# Run the benchmarks and tests (inside or outside a container)
#===============================================================================

# Just an example of ONE benchmark you might run:
bench: ./bin/criterion-interactive docker
	stack bench --no-run-benchmarks
#	./bin/criterion-interactive ./criterion-external/time_interactive.sh
#	./bin/criterion-interactive ./go_bench.sh sumtree ST 5 -- -o report.h
	./bin/criterion-interactive stack exec -- bench-cursor sumtree packed 5 -- -o report.h

# Test with both pure and mutable cursor implementations:
test:
	stack test --flag Examples:pure
	stack test --flag Examples:-pure


clean:
	rm -rf bin/*

.PHONY: all test debug bench clean docker
