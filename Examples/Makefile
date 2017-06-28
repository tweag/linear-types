

all: ./bin/criterion-interactive
	stack docker pull
# quick test:
	stack test

# The Dockerfile in this directory is for debugging
debug:
	docker build -t debug/linear-types .
#	stack --docker-image debug/linear-types build
	stack --docker-image debug/linear-types test --no-run-tests
	stack --docker-image debug/linear-types exec bash

./bin/criterion-interactive:
	mkdir -p ./bin
	cd ./criterion-external; stack install --local-bin-path=../bin


# Just an example of ONE benchmark you might run:
bench: ./bin/criterion-interactive
	stack bench --no-run-benchmarks
#	./bin/criterion-interactive ./criterion-external/time_interactive.sh
#	./bin/criterion-interactive ./go_bench.sh sumtree ST 5 -- -o report.h
	./bin/criterion-interactive stack exec -- bench-cursor sumtree packed 5 -- -o report.h

test:
	stack test --flag Examples:pure
	stack test --flag Examples:-pure

clean:
	rm -rf bin/*

.PHONY: all test debug bench clean
