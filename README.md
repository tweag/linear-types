Retrofitting linear types: artifact repository
==============================================

This artifact is composed of the Linear Haskell GHC prototype and
case-studies for the article _Retrofitting linear types_ accepted at
POPL'18. Details of individual case studies can be found in
[the dedicated section below](#section-5-evaluation-and-case-studies)

To clone this repository at the appropriate commit:

    $ git clone --recursive --single-branch -b artifact https://github.com/tweag/linear-types.git
    $ git checkout <TODO:COMMIT NUMBER>

Alternatively you can download the [Virtual Machine
image](full-virtual-machine) which contains all the material for this
artifact.

Quick Start Instructions
========================

This artifact consists of the tarball or Git checkout that contains
this README, plus the modified version of GHC
[found on Github](#section-4-implementation).  We will refer to the
machine you downloaded this artifact to as the "host system".  We
assume that you follow this guide starting from the directory that
contains this file.

The easiest way to use this artifact is to rely on the Docker support,
including pre-built images that are hosted by dockerhub.com. The host
system needs only GNU make plus an installation of Docker:
   https://docs.docker.com/engine/installation/
   
If Docker is not a convenient solution we provide a Virtual Machine
(see [Alternative installation methods](#alternative-installation-methods)).

We have tested this artifact with Linux as the host system, but Mac OS
with the Docker CLI should work as well.

The following one-liner will bring up a ghci interpreter with support
for linear types:

    $ docker run -it tweag/linear-types:popl18

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

### Software to run the benchmarks

To get ready to run the benchmarks from section 5.1, you'll have to
install some additional software.  Ultimately, the code/data you need
will fall into three buckets:

 (1) modified GHC with linear types
 (2) benchmark programs and supporting scripts
 (3) resulting benchmark data and plots

If using Docker, you can run all three steps inside Docker building
three different docker images.  They will have these names respectively:

 * tweag/linear-types
 * parfunc/linear-haskell-popl18-artifact
 * parfunc/linear-haskell-popl18-artifact-plots
 
But it's also possible to download the Docker image for (1), and then
build (2) via the Haskell stack tool (using its underlying Docker
integration).  Our goal is to maximize flexibility, and thus give the
reader of this artifact workarounds in case of any problems.


## Alternative installation methods

### Full Virtual Machine

If you don't want to use Docker, you can use a full virtual machine
found at the following address:

  http://TODO:FINISHME-URL-HERE

Import the virtual machine into VirtualBox. The virtual machine runs
lubuntu and has all the necessary dependencies and source code for
this artifact. The virtual machine does not have docker, so follow the
dockerless instructions below

Your username is _ubuntu_ and your password _ubuntu_.

#### Guest additions

If you want to benefit from a shared clipboard between the virtual
machine and your computer, you will need to install the Virtualbox
guest additions.

- Add an optical drive to the newly imported virtual machine
  (settings > storages > add optical drive)
- Start the virtual machine
- Use Virtualbox's menu above the virtual machine:
  Devices > insert guest additions CD image
- The guest additions CD will appear on the desktop. Open with
  right-click > open in terminal
- Run `$ sudo ./VBoxLinuxAdditions.run` (your password is _ubuntu_)
- In Virtualbox's menu above the virtual machine:
  Device > Shared Clipboard > Bidirectional (or the setting that you like)
- Reboot the machine (_e.g._ `$ sudo reboot 0`)

#### Navigating the machine

The source code for the artifact is in the directory `~/artifact`. You
will also find the source code for linear GHC (see
[implementation](#section-4-implementation)) in `~/ghc_linear`. The
git directories are preserved in order to be able to inspect history.

To open a terminal window, choose System tools > LXTerminal in the
desktop's global menu.

To install additional packages, use (once, in order to get the package
lists)

    $ sudo apt update

then

    $ sudo apt install <desired packages>

Your password is _ubuntu_.

### Full source-based installation

If instead you want to build everything directly on the host system
without any kind of virtualization or containerization, you will need
to follow these steps:

 * Build and install the modified [GHC from Github](#section-4-implementation).
   Make sure that linear version of `ghc` is in PATH (version 8.2.0.20170809).
 * Run `$ stack --no-docker test` in this directory, with
   the modified GHC in scope.
 * Run `$ STACK_ARGS=--no-docker ./run_all_cursor_benches.sh` to run all
   the benchmarks.
 * Run `$ cd plots && make`

You can look at `Dockerfile` and `deps/ghc-docker/Dockerfile` for
example commands to install the dependencies, such as GNU plot.

Basic Tests
===========

Once you've downloaded this artifact, you can run some internal tests.
If you have stack and Docker on the host system, then you can test
simply with:

	$ stack docker pull
    $ stack test --flag Examples:-pure
    $ stack test --flag Examples:pure

In the virtual machine there is no docker but all the dependencies are
installed use the following instead:

    $ stack --no-docker test --flag Examples:pure
    $ stack --no-docker test --flag Examples:-pure

If you don't have stack, then you will want to do everything inside
Docker, where a version of stack is included:

    $ docker run -it parfunc/linear-haskell-popl18-artifact:0.0.9 bash
    $ stack --no-docker test --flag Examples:pure
    $ stack --no-docker test --flag Examples:-pure

The above `docker run` command will download the precached binary
version from dockerhub.  If you would rather spend CPU time than
download bandwidth, you can build the image yourself with by running
the following before the above commands:

    $ make build

(Likewise you can build the `tweag/linear-types` GHC image with the
script `deps/ghc-docker/update-docker.sh`).

You may want to look through the `Makefile` contained in this
directory, as it provides alternative ways of doing things, as well as
examples of commands you may want to run.

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

Because we haven't, as of yet, modified the types of function in
Haskell's standard library, we rewrote, for our purposes, a few
standard library functions with linear types in the
[`src/Linear/`](src/Linear/) directory.

### Section 5.1

In this section, the main task is to benchmark different approaches to
operating on serialized tree data, and in particular the "type safe
linear cursors" approach.

If you built or fetched the artifact (2), corresponding to the Docker
image `parfunc/linear-haskell-popl18-artifact`, then you already have
a binary executable for the benchmark harness as well as the scripts
that run it.

To run the benchmarks fully inside docker, you only need to do this:

    $ cd plots
    $ make docker-bench

That will build the third docker image, run benchmarks, store the
resulting plots inside it, and finally extract the plots back to the
host system.  It will take a while.

Benchmarking inside Docker should have neglible impact for this
example, because the benchmark program does not perform file or
network IO.

However, if the host system happens to be Linux, you may be able to
run the benchmarks outside Docker, with:

    $ make run-bench
    $ cd plots
    $ make

The virtual machine has the required dependencies to run the above
commands though, of course, the benchmark results may be unreliable.

### Section 5.2

The implementation of the socket abstraction with typestate depends on
the [`src/Socket/IO.hs`](src/Socket/IO.hs) module to represent the
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

The implementation of a pure API on top of a mutable API, described in
Section 5.3 of the article, is implemented in
[`src/Purify.hs`](src/Purify.hs).

The names are a bit different than in the article, where things have
been simplified a little: mutable trees are named `MTree` and
immutable ones are named `Tree`. The API function that is exposed is
`updateTree`.

Compared to Haskell SpriteKit, which inspired this example, we don't
implement many of the optimisation which are necessary make this sort
of abstraction efficient. But this optimisation code would occur
entirely in the unsafe, non-linear code, where we have access to
exactly the same programming techniques as Haskell SpriteKit.

The only place where linearity comes into play is in the `updateTree`
function, where it is a limitation posed on the caller in order to
ensure safety.

Tests for this implementation appear under the heading "Purify" when
running the command

```
$ stack test
```

These tests are implemented in
[`test/PurifySpec.hs`](test/PurifySpec.hs).
