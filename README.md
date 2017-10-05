## TODOs

- [ ] Suggest to ignore the many compilation warnings
- [ ] Instruction to compile with different implementation for cursors
- [ ] Instruction to interpret the benchmark reports
- [ ] Don't forget `git submodule update --init` in instructions and packaging


Retrofitting linear types: artifact repository
==============================================

This artifact is composed of the case-studies for the article
_Retrofitting linear types_ accepted at POPL'18. Details of individual
case studies can be found in [the dedicated section
below](#section-5-evaluation-and-case-studies)


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
    
You may also check that the following non-linear function raises a
type error:

    g :: Int ⊸ (Int,Int) ; g x = (x,x)

Note that the current prototype only supports the unicode version of
the linear arrow (⊸).  There is not yet an ASCII syntax.  Further, the
standard libraries have not yet been modified to linearize function
types, so only the very basics will be usable in linear function
definitions. See [below](#section-4-implementation) for more details.


If instead............
[source installation](#source-installation)

Article sections
================


Section 4: Implementation
-------------------------

Our current implementation of linear types can be found at the git
commit reference
[9cf8f718b26aeacd5b5fc95cfe583e6b78e48d2f](https://github.com/tweag/ghc/commit/9cf8f718b26aeacd5b5fc95cfe583e6b78e48d2f)
(this reference can also be found in the
[`Dockerfile`](deps/ghc-docker/Dockerfile) that we use to build the
Docker images). It is implemented on top of the commit
[9410a4c8a710fc59ad8b03b94302d7cb6b9c92f3](https://github.com/ghc/ghc/commit/9410a4c8a710fc59ad8b03b94302d7cb6b9c92f3).

You can inspect the diff for the entire implementation with the
following commands:

```
$ git clone https://github.com/tweag/ghc && cd ghc
$ git diff 9410a4c8a710fc59ad8b03b94302d7cb6b9c92f3 9cf8f718b26aeacd5b5fc95cfe583e6b78e48d2f
```

Use the following variant of `git diff` to get a summary of the changes
```
$ git diff --stat 9410a4c8a710fc59ad8b03b94302d7cb6b9c92f3 9cf8f718b26aeacd5b5fc95cfe583e6b78e48d2f
```

To go further, our implementation comes with a
[README](https://github.com/tweag/ghc/blob/9cf8f718b26aeacd5b5fc95cfe583e6b78e48d2f/README.md),
with detailed usage instructions.

Bare in mind that this implementation is still a prototype, and there are still various
ways to fool the type checker into accepting non-linear
definitions. The README has a [list of known
ones](https://github.com/tweag/ghc/blob/9cf8f718b26aeacd5b5fc95cfe583e6b78e48d2f/README.md#bugs).

Section 5: Evaluation and case studies
--------------------------------------

### Section 5.1


### Section 5.2


### Section 5.3


Source installation
===================
