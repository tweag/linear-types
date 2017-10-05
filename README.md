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

As mentionned in the article, our prototype only implements
monomorphic multiplicities. Polymorphic multiplicities as well as
multiplicity-parametric types are missing. Our case studies don't need
these missing features except the socket example in [Section
5.2](section-5-2), where we had to work around it.

Section 5: Evaluation and case studies
--------------------------------------

### Section 5.1


### Section 5.2

The implementation of the socket abstraction with typestate depends on
the [`src/IO.hs`](src/IO.hs) module to represent the
multiplicity-parametric IO monad (which we name `IO'` in the
implementation), as described in the article. As
multiplicity-parametric data types are not implemented in our
prototype, as mentionned [above](section-4-implementation), we emulate
multiplicity parametricity using a type family.

This puts this use-case on shiftier grounds than more the other case
studies: it is quite easy, still, to fool the type-checker into
accepting unsafe, non-linear, functions where linear functions are
expected.

The implementation of the abstraction is done in
[`src/Socket/Generic.hs`](src/Socket/Generic.hs), where we go beyond
what the article describes and don't actually specify the type-level
automaton which describes the evolution of the socket's
typestate. That is: neither the precondition, nor the postcondition
the API functions are fixed. Instead, all the API functions are
parametrised by the type-level automaton, given as a typeclass. The
reason for this is that the actual protocol sequence of actions to
take with a socket depends on the network protocol of the socket
(_e.g._ TCP, UPD, …).

This `src/Socket/Generic.hs` module is implemented as a wrapper around
the `socket` library, and illustrate how we intend to use linearity to
add guarantees to APIs which are not necessarily defined in terms of
linearity. Some complications occur, however, due to the fact that the
library's `IO` and our `IO'` are different types, and `IO` is treated
specially by Haskell.

The `Generic` API is not safe, per se: when defining a protocol, it is
the library writer's responsibility to provide the rules that sockets
of this protocol must obey. This is done in file
[`src/Socket.hs`](src/Socket.hs) for the case of TCP. It is convenient
to also give a specialised type to API functions at a given protocol
because the types become more simpler and help type inference a
lot. We also do this in `src/Socket.hs`.

Finally, you can find a small example of usage of this API in
[`scr/SocketExample.hs`](src/SocketExample.hs). But we have not
provided tests to run it.

### Section 5.3


Source installation
===================
