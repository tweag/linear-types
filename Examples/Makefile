

all:
	stack docker pull
	stack test

# The Dockerfile in this directory is for debugging
debug:
	docker build -t debug/linear-types .
#	stack --docker-image debug/linear-types build
	stack --docker-image debug/linear-types test --no-run-tests
	stack --docker-image debug/linear-types exec bash

test:
	stack test --flag Examples:pure
	stack test --flag Examples:-pure

.PHONY: all test debug
