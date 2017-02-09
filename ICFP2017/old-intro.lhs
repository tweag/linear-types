
\section{Introduction}

\rn{I think this intro can be focused and tightened up significantly.  SPJ may
  be interested in doing one in his widely-loved intro style.  Or I'm happy to
  take a stab at it.}

Several recent advances in typed functional programming applied
research have focused on extending type systems to make it easier to
encode strong invariants key to the {\em correctness} of programs.
Extensions from GADTs \cite{xi_guarded_2003}, to type-level functions
such as type families \cite{chakravarty_associated_2005-1}, to
increasingly automatic and complete promotion of term-level data types
to the type-level \cite{eisenberg_promoting_2014}. Yet in practice,
that a user's program is denotationally correct with respect to some
abstract specification matters little if does not abide to efficient
and timely release of scarce hardware resources. Indeed, {\em
  predictable} and {\em easy to reason about} use of resources is
frequently part of the specification too. We argue that teaching the
type system to track resources and their lifetimes will prove crucial,
for many applications, to resolving the impedance mismatch between the
expressive power of high-level programming languages and the age-old
low-level concerns of taming memory consumption and running fast on
real hardware.

\subsection{Resource tracking}

Scarce system resources include memory mappings, locks, sockets and
file handles, among others.  For instance, with no primitive support from the
programming language for managing these resources, acquiring a file
handle for reading and then disposing of a file handle looks something
like this:
\begin{code}
do  h <- openfile "myfile" ReadMode
    ...     -- some code that reads the file
    hClose h
\end{code}
This style of programming is unsafe. In the above style, there is nothing
preventing the programmer from accidentally reusing the file handle
after calling |hClose|, even though the handle is defunct forever
in the future, or indeed call |hClose| twice. In short, programming
with explicit file handle creation/deletion operators is prone to the
same bugs that plague programming with explicit
allocation/deallocation memory operators. Two common strategies to
avoid the bane of use-after-free and free-after-free bugs are:

\begin{enumerate}
\item restrict programs to using specifically provided higher-level
  combinators or patterns of programming that reduce their likelihood,
  as in streaming I/O frameworks and the RAII pattern popularized by
  modern C++. This is the purpose of various Haskell stream processing
  libraries such as iteratees~\cite{kiselyov_iteratees_2012},
  conduit~\cite{snoyman_conduit_2015},
  pipes~\cite{gonzalez_pipes_2015}, and
  machines~\cite{kmett_machines_2015}. The sheer number of libraries
  aiming at tackling this problem space speaks to its difficulty. None
  subsumes the others in expressive power.
\item make resource disposal implicit and completely automatic via a
  garbage collection (GC) mechanism. Kiselyov
  \cite{kiselyov_iteratees_2012} argues against fully automatic
  resource management for managing I/O resources, such as file
  descriptors and buffers. In particular, relying on the garbage
  collector to reclaim file descriptors, leads to file descriptor
  leaks.  In general, the problem with automatic resource management
  is that the runtime provides no guarantees as to the timeliness of
  the resource reclaiming process. File handle finalizers might run at
  an arbitrarily late time in the future. Locks are certainly a bad
  idea to release automatically for this reason.
\end{enumerate}

We propose to follow a third approach: tracking resources in the type
system. In fact, a cornerstone of the Rust programming
language~\cite{matsakis_rust_2014} is that it provides this resource
safety out-of-the-box. Through its borrow checker, Rust captures a
notion of affine types in its type system. The lifetime analysis is
powerful enough to, for example, ensure that a file handle never escapes
the current lexical scope:

\improvement{code alignment}
\begin{verbatim}
{
  let path = Path::new("hello.txt");
  let mut file = try!(File::open(&path));
  ... // some code that reads the file
}
// The variable `path` falls out of scope. Rust prevents `path`
// from exiting this scope, as part of a closure or otherwise.
// Therefore the file can be, and in fact is, closed when
// this scope ends.
\end{verbatim}

The lifetime analysis in Rust makes it possible to remain resource
safe without losing much expressive power at all.

\subsection{Memory management}

A central tenet of this paper is,
\begin{center}
\em memory is just a system resource like any other, which, as such,
deserves the parsimonious consumption and timely release that other
resources can.
\end{center}
Fully automatic memory management is certainly convenient, and an
effective means of avoiding use-after-free and free-after-free bugs,
since it is the language runtime that guarantees, via a global dynamic
analysis, that resources are reclaimed only when it is entirely safe
to do so. But this analysis is expensive to run. For
this reason, resources are reclaimed in batches, to amortize its cost,
only when resource pressure is deemed to warrant reclaiming 
resources. Worse, this global analysis, aka garbage
collection, often requires exclusive access to resources, hence
stalling and potentially starving other threads of control.

In interactive low-latency systems (web servers, graphical user
interfaces, high-speed trading systems, real-time analytics and query
services, games, etc), pausing threads performing useful work is
problematic. Because these pauses can happen at any time, for
indeterminate periods of time, an unbounded number of times, the
tail-end of runtime distributions increases. This in turn makes
synchronization among many threads more costly and less frequent,
because threads can only synchronize as often as the last thread
reaches the synchronization point.

Speeding up this global analysis, be it by considering only a portion
of the entire heap of resources most of the time (generational GC's),
making the analysis interruptible (incremental GC's) or coalescing
resources into coarser grained units that are reclaimed atomically
(compact regions), is a decent workaround for many applications. But
better yet not have to perform this analysis at all! Or over a much
smaller heap.

Whereas GC pauses have frequently been observed to reach 50ms or more
for large heaps of long-lived
objects\footnote{\url{https://blog.pusher.com/latency-working-set-ghc-gc-pick-two/}},
games typically target a maximum latency budget of 16ms per rendered
frame, corresponding to a 60 frames per second refresh rate. Whereas
incremental GC's might target single digit millisecond latencies,
often at a substantial cost on throughput, bulk synchronous parallel
programs (see below) synchronize over networks with single digit
microsecond roundtrip latencies.\improvement{Probably: do not cite BSP yet,
  instead speak of HPC workloads}

\subsubsection{Latency matters}

The following example is extracted from a real-world business
use case at Pusher, cited above. The challenge is to maintain a
concurrent queue of messages. Each message can be of arbitrary size,
but usually in the order of kilobytes. There can be many hundreds of
thousands of message to maintain in memory. Old messages are evicted,
upon being read by clients, or if the queue grows too long (so it is
okay to lose messages). Any client can also request for any message in
the queue to be removed. In short, the concurrent queue supports the
following operations:
\rn{This still bothers me.  I'd really like to change it to
  include MsgId.  \verb|push :: Queue -> MsgId -> Msg -> IO ()|.}
\begin{code}
push :: Queue -> Msg -> IO ()
delete :: Queue -> Msg -> IO ()
-- Remove the N oldest messages.
evict :: Queue -> Int -> IO (Vector Msg)
\end{code}

If the queue grows very large, then most objects in the queue are very
long-lived. This runs counter to the ``generational hypothesis'' that
is so crucial to the performance of generational garbage collectors.
In this example, most objects that get created do {\em not} die
shortly after being created. So a partial sweep of only the most
recent allocations is unlikely to find any garbage. Yet performing
a full sweep of the entire object graph is onerous, and wasteful.

The latency observed on this use-case caused Pusher to walk away from
Haskell\footnote{\url{https://blog.pusher.com/golangs-real-time-gc-in-theory-and-practice/}}. Such
a queue is representative of one use-case which motivated this work:
an in-memory cache for a distributed on-disk object storage system.

\paragraph{bulk synchronous programming} A very popular model for
applications in high-performance computing is bulk synchronous
parallelism \cite{valiant_bridging_1990}. In this model, computations
are structured as iterating a three step process:
\begin{description}
\item[Compute:] simultaneously start as many threads as there are
  cores in the cluster, each computing over a subset of the data.
\item[Communicate:] all processes communicate results with other nodes
  (\emph{e.g.} their neighbors in a mesh physics simulation).
\item[Synchronize:] the next iteration does not start until all threads
  synchronize on a global write barrier.
\end{description}
A new cycle begins when a previous one finishes. Even interactive user
queries with a total latency envelope of 100ms can be processed as a
sequence of dozens of such parallel phases. The message sends of the
communicate phase can be performed across a cluster in mere
microseconds on current hardware.

As we start increasing the number of threads to synchronize on the
global barrier to thousands of threads and beyond, any variance in the
thread runtimes increases the time to fully reaching the barrier for
all threads. Performance crucially depends on achieving predictable
latencies, because the lower the variance, the tighter we space each
barrier in time, and the less threads sit idle waiting on their peers.

There are of course ways to perform latency hiding. Threads can be
oversubscribed, data can be prefetched, or de-normalized (made
redundant copies of in many locations) and computations duplicated to
reduce the number of neighbours threads have to communicate with.
These solutions all come at a complexity cost in systems that have
often already far exceeded any reasonable complexity budget.
Maintaining low and predictable latencies is therefore a means to
achieve simpler designs.

\paragraph{Stream processing} The Square Kilometer
Array\footnote{\url{https://www.skatelescope.org/}} is projected to produce
hundreds of terabytes per second of raw data each second streaming
from its thousands of sensors. Keeping up with such a deluge requires
processing the data over multiple machines at once, since the
necessary throughput far exceeds the memory bandwidth of a single
machine. Yet as we scale up the amount of hardware resources that we
throw at a problem, it is the total energy cost of the system that
eventually becomes a bottleneck \cite{doe_exascale_2010}. The total
amount of memory available on each machine is ultimately limited by
cost and energy requirements. This means that there is only so much
data that can remain in-flight in the system at any given time. The
mean throughput of a steady state system is governed by Little's law
\cite{little_proof_1961}:

\begin{displaymath}
  \textrm{mean throughput} = {\textrm{mean number of in-flight
      requests} \over \textrm{mean request latency}}
\end{displaymath}

Since the number of in-flight requests is limited by the available
memory, higher throughput can only be achieved by decreasing
latencies. In such a setting, GC productivity becomes crucial to
optimize for.

\subsubsection{Easing GC pressure with compact regions}

In general, in any mark-and-sweep GC the time necessary for a full
garbage collection pass is proportional to the amount of live data in
memory. Or rather, to the number of objects. A recent proposal
\cite{yang_compact_2015} has suggested that an effective means of
reducing the number of objects that the GC needs to traverse is to
{\em compact} many long-lived objects into a single immutable chunk of
memory. In effect, the lifetimes of these objects are assumed equal.
The GC can pretend that the chunk is a single object because objects
inside it live and die together, in one fell swoop.

This approach is certainly a useful tool for the discriminating
high-performance programmer. We believe that tracking resources in the
type system can work hand-in-hand to enhance the power of this tool.

Consider the queue example again. One possible implementation strategy
consists in representing the queue as a chain of compact regions
holding $k$ messages rather than a chain of messages. This will indeed
reduce the pressure on the garbage collector. But at the cost of
having the |push| operation have an $O(k)$ worst-case time due to
sealing a region.

\subsubsection{the allocation hierarchy}

Because either memory allocation or memory reclamation (but often
both) are expensive operations, it becomes increasingly harder to fit
within a set latency budget the further down the ``allocation
hierarchy'' we go:
\begin{enumerate}
\item {\bf No allocation:} The cheapest allocation is the one that
  does not exist. Any allocation guaranteed by the compiler not to
  occur is one that does not eat into the application's small latency
  budget, and that's a fact the programmer can count on.
\item {\bf Off GC-heap allocation:} if you must allocate, then better
  allocate outside of the GC's bailiwick, in a separate memory region.
  In this way, the size of the GC heap does not increase, so GC pauses
  are shorter and farther between.
\item {\bf On GC-heap allocation:} If neither of the above are
  possible, or for small short-lived objects that never graduate
  beyond a generation-0 garbage sweep, which is cheap, then perhaps
  playing it fast and loose by allocating in the main heap and letting
  the GC take care of the rest can be acceptable.
\end{enumerate}

We propose, in this article, an extension to Haskell's type system,
which we call \HaskeLL{}. \HaskeLL fits the top two tiers of this
hierarchy:\improvement{we mostly address (2) in this article, though
  we keep fusion very much in mind, probably rephrase}
\begin{enumerate}
\item Fusion is a common technique for statically eliminating
  redundant allocations while retaining good code modularity. While
  first-class type system support for tracking resources certainly
  is not a necessity to perform fusion, a common complaint born out of
  using \verb|RULE| pragma based fusion on large codebases is that it
  is brittle and hard to reason about. Our type system {\em
    guarantees} fusion where the programmer has expressed an intent.
  It can therefore guarantee the absence of allocation at precise
  points in the program. Crucially, this guarantee is robust in the
  face of compiler optimizations.
\item where allocation cannot be avoided without trading in an
  excessive time budget, we allow safely allocating in a dedicated
  heap not managed by the GC, where objects can be deallocated
  explicitly at exactly the right time, yet without compromising
  memory safety.
\end{enumerate}
\subsection{Contributions}

The design for \HaskeLL{} is backed by a core calculus \calc{}.
\calc{} is a linearly-typed extension of the $λ$-calculus with data
types, with the following characteristics:

\begin{itemize}
\item Implicit conversions to and from the linear world and
  the unrestricted world, together with linearity polymorphism for
  higher order functions.
\item A lazy dynamic semantics which include explicit deallocation of
  linear data.
\item Is designed to be compatible with in an existing rich programming
  language. 
  \todo{Do we speak of the prototype at this point? I
    [aspiwack] would rather leave it at that and prove this assertion
    in the body of the article by citing the prototype (and maybe some
    GHC things with which we are compatible: \emph{e.g.} the kind
    system (which is not affected) and dependent types).}
\end{itemize}
