## TODOs

- [ ] Suggest to ignore the many compilation warnings
- [ ] Instruction to compile with different implementation for cursors
- [ ] Instruction to interpret the benchmark reports
- [ ] Don't forget `git submodule update --init` in instructions and packaging


# Retrofitting linear types: artifact repository

This artfiact ..............


Quick Start Instructions
========================

The easiest way to use this artifact is to rely on the Docker support,
including pre-built images that are hosted by dockerhub.com.  The host
system needs only an installation of Docker: 
   https://docs.docker.com/engine/installation/

You can bring up a ghci interpreter with linear types 

    docker run -it tweag/linear-types:popl18

After which you can type in a simple function with a linear type:

    f :: Int ⊸ Int; f x = x

Note that the current prototype only supports the unicode version of
the linear arrow (⊸).  There is not yet an ASCII syntax.  Further, the
standard libraries have not yet been modified to linearize function
types, so only the very basics will be usable in linear function
definitions.


If instead............
[source installation](#source-installation)


=====================


Section 4: Benchmarks
---------------------

### Section 4.1


### Section 4.2


### Section 4.3


Section 5: Implementation
-------------------------




Source installation
===================
