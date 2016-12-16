% -*- latex -*-
% Created 2016-09-15 tor 14:09
\documentclass[11pt]{article}
%include polycode.fmt
%format .         = ". "
%format forall a         = "∀" a
%format _ (a)         = "_{" a "}"
%format ω = "\omega"
%format π = "\pi"
%format ρ = "\rho"
%subst keyword a = "\mathsf{" a "}"
\usepackage[backend=biber,citestyle=authoryear,style=alphabetic]{biblatex}
\bibliography{PaperTools/bibtex/jp.bib}
\usepackage{graphicx}
\usepackage{grffile}
\usepackage{longtable}
\usepackage{wrapfig}
\usepackage{rotating}
\usepackage[normalem]{ulem}
\usepackage{amsmath}
\usepackage{amsthm}
\usepackage{textcomp}
\usepackage{amssymb}
\usepackage{capt-of}
\usepackage[dvipsnames]{xcolor}
\usepackage{hyperref}
\hypersetup{
    colorlinks,
    linkcolor={red!50!black},
    citecolor={blue!50!black},
    urlcolor={blue!80!black}
  }
\usepackage{mathpartir}
\usepackage{fontspec}
\usepackage{unicode-math}
\usepackage[plain]{fancyref}
\def\frefsecname{Section}
\def\freffigname{Figure}

% \setmonofont[Scale=0.8]{DejaVu Sans Mono}
% \setmonofont{CMU TypeWriter Text}
% \setmainfont[ExternalLocation=/Library/Fonts/,Ligatures={Common,Rare,Historic},Variant=1]{Zapfino.ttf}
% \setmainfont{DejaVu Sans}
% \setmainfont{TeX Gyre Pagella}
% \setmathfont{TeX Gyre Pagella Math}
% \setmainfont{Latin Modern Roman}
\setmathfont[ExternalLocation=fonts/]{latinmodern-math}
\setmainfont[ExternalLocation=fonts/,
ItalicFont=lmroman10-italic,
BoldFont=lmroman10-bold,
]{lmroman10-regular}

\newcommand{\case}[3][]{\mathsf{case}_{#1} #2 \mathsf{of} \{#3\}^m_{k=1}}
\newcommand{\data}{\mathsf{data} }
\newcommand{\where}{ \mathsf{where} }
\newcommand{\inl}{\mathsf{inl} }
\newcommand{\inr}{\mathsf{inr} }
\newcommand{\flet}[1][]{\mathsf{let}_{#1} }
\newcommand{\fin}{ \mathsf{in} }
\newcommand{\varid}[1]{\ensuremath{\Varid{#1}}}
\newcommand{\susp}[1]{⟦#1⟧}

\newcommand{\figuresection}[1]{\textbf{#1}}
\newenvironment{aside}
{\quotation{} \scriptsize \noindent Side remark. }
{ End of side remark. \endquotation }

\usepackage[colorinlistoftodos,prependcaption,textsize=tiny]{todonotes}
\usepackage{xargs}
\newcommandx{\unsure}[2][1=]{\todo[linecolor=red,backgroundcolor=red!25,bordercolor=red,#1]{#2}}
\newcommandx{\info}[2][1=]{\todo[linecolor=OliveGreen,backgroundcolor=OliveGreen!25,bordercolor=OliveGreen,#1]{#2}}
\newcommandx{\change}[2][1=]{\todo[linecolor=blue,backgroundcolor=blue!25,bordercolor=blue,#1]{#2}}
\newcommandx{\inconsistent}[2][1=]{\todo[linecolor=blue,backgroundcolor=blue!25,bordercolor=red,#1]{#2}}
\newcommandx{\improvement}[2][1=]{\todo[linecolor=Plum,backgroundcolor=Plum!25,bordercolor=Plum,#1]{#2}}
\newcommandx{\resolved}[2][1=]{\todo[linecolor=OliveGreen,backgroundcolor=OliveGreen!25,bordercolor=OliveGreen,#1]{#2}} % use this to mark a resolved question
\newcommandx{\thiswillnotshow}[2][1=]{\todo[disable,#1]{#2}} % will replace \resolved in the final document

% Link in bibliography interpreted as hyperlinks.
\newcommand{\HREF}[2]{\href{#1}{#2}}

\newtheorem{definition}{Definition}
\newtheorem{lemma}{Lemma}

\newcommand\HaskeLL{HaskeLL}
\newcommand\calc{{\ensuremath{λ^q}}}

\author{Mathieu Boespflug and Arnaud Spiwack}
\date{\today}
\title{The case for resource aware type systems}
\hypersetup{pdflang={English}}

\begin{document}

\maketitle
\begin{abstract}
Correctly programming system resources is a perilous proposition. For
this reason, many high-level programming languages let the programmer
delegate freeing resources to a background thread that does so
dynamically, not at statically defined points in the control flow. We
detail the challenges of dynamic resource management and make the case
for an alternative solution to the problem that can be combined with
dynamic resource management: guaranteeing resource safety through
static analysis.
\end{abstract}

\section{Introduction}

Several recent advances in typed functional programming applied
research have focused on extending type systems to make it easier to
encode strong invariants key to the {\em correctness} of programs.
Extensions from GADT's \cite{xi_guarded_2003} (now in both GHC and
OCaml), to type-level functions such as type families
\cite{chakravarty_associated_2005-1}, to increasingly automatic and
complete promotion of term-level data types to the type-level
\cite{eisenburg_promoting_2014}. Yet in practice, that a user's
program is denotationally correct with respect to some abstract
specification matters little if does not abide to efficient and timely
release of scarce hardware resources. Indeed, {\em predictable} and
{\em easy to reason about} use of resources is frequently part of the
specification too. We argue that teaching the type system to track
resources and their lifetimes will prove crucial, for many
applications, to resolving the impedance mismatch between the
expressive power of high-level programming languages and the age-old
low-level concerns of taming memory consumption and running fast on
real hardware.

\subsection{Static resource tracking}

Scarce system resources include memory mappings, locks, sockets and
file handles, among others. With no primitive support from the
programming language for managing these resources, acquiring a file
handle for reading and then disposing of a file handle looks something
like this:
\begin{code}
do  h <- openfile "myfile" ReadMode
    ...     -- some code that reads the file
    hClose h
\end{code}
This style of programming is unsafe. In the above, there is nothing
preventing the programmer from accidentally reusing the file handle
after calling |hClose|, even though the handle is now defunct forever
in the future, or indeed call |hClose| twice. In short, programming
with explicit file handle creation/deletion operators is prone to the
same bugs that plague programming with explicit
allocation/deallocation memory operators. Two common strategies to
avoid the bane of use-after-free and free-after-free bugs are:

\begin{enumerate}
\item restrict programs to using specifically provided higher-level
  combinators or patterns of programming that reduce their likelihood,
  as in streaming I/O frameworks and the RAII pattern popularized by
  modern C++;
\item make resource disposal implicit and completely automatic via
  a garbage collection (GC) mechanism;
\end{enumerate}

Each of these is the topic of the next two headings. Higher-level
combinators fall short of enforcing all the resource management
correctness invariants we would like. Further, they impose a sometimes
substantial encoding overhead. While automatic resource disposal is
a problematic source of non-determinism that can be the cause of
subtle performance and/or correctness bugs.

\subsection{Combinator libraries}

Combinator libraries strive to provide both soundness and timely
release of resources by restricting the available programming
model. Libraries such as iteratees~\cite{kiselyov_iteratees_2012},
conduit~\cite{snoyman_conduit_2015}, pipes~\cite{gonzalez_pipes_2015},
and machines~\cite{kmett_machines_2015} offer stream-processing
combinators to that effect.

The sheer number of libraries aiming at tackling this problem space
speaks to its difficulty. None subsumes the others in expressive power.

Machines~\cite{kmett_machines_2015} are pure stream processors: they cannot return a value which
is not a stream (for instance the size of its input), while Conduits~\cite{snoyman_conduit_2015}
can easily do that. To express a simple line count example, we will need
the following subset of the Conduit API:
\begin{code}
-- Provides a stream of output values,
-- without consuming any input or producing a final result.
type Producer m o = forall i. ConduitM i o m ()

(=$=)  :: Monad m
       => ConduitM a b m ()
       -> ConduitM b c m r
       -> ConduitM a c m r
map :: Monad m => (a -> b) -> ConduitM a b m ()

-- Chop up stream of strings along line boundaries.
linesUnbounded :: ... => ConduitM ByteString ByteString m ()
sourceFile  :: ... => FilePath -> Producer m a
\end{code}
Given the above, we can implement a simple line count in Conduit:
\begin{code}
wcConduit :: ... => FilePath -> ConduitM () Void m Int
wcConduit rp = do
    Sum i <- sourceFile rp =$=
             linesUnbounded =$=
             map (\_ -> Sum 1) =$=
             fold
    return i
\end{code} % $

Unlike lazy I/O, exactly the amount of requested input is read at each
step of the computation (no silent readahead), is guaranteed to run in
constant memory if the line length is bounded, and disposes of any
file handles at precisely the point where we |run| the |ConduitM|
monad. However, once one starts to manipulate multiple input streams
at once, things become tricky.

Like Conduits, the Machines library provides a set of combinators for
splicing together stream computations, as well merging them and
splitting them.
\begin{code}
-- A machine reads from |k| inputs
-- and may yield |o| results before stopping.
data Machine (k :: * -> *) o

data T a b :: * -> * where
  L :: T a b a
  R :: T a b b

-- Machine that reads either an |a| or a |b| to produce |c|'s.
type Tee a b c = Machine (T a b) c

fit :: (forall a. k a -> k' a) -> Machine k o -> Machine k' o

-- A small EDSL for expressing machines.
data Plan (k :: * -> *) o a

awaits :: k i -> Plan k o i
yield :: o -> Plan k o ()
-- Interpret the plan into an action machine.
repeatedly :: Plan k o a -> Machine k o
\end{code}
With these basic verbs in place, it becomes possible to express stream
computations that operate over multiple inputs at once.
\begin{code}
data Three a b c x where
  A :: Three a b c a
  B :: Three a b c b
  C :: Three a b c c

-- tuples up the data from three input streams
interleave3 :: Machine (Three a b c) (a,b,c)
interleave3 =
    repeatedly $ do
    a <- awaits A
    b <- awaits B
    c <- awaits C
    yield (a,b,c)

-- read one value from an input stream and two from another
interleave12 :: forall a b. Tee a b (a,b,b)
interleave12 =
    fit dup2 interleave3
  where
    dup2 :: forall x. (Three a b b x) -> (T a b x)
    dup2 A = L
    dup2 B = R
    dup2 C = R
\end{code} % $

In sum, each pattern of access to streamed system resources gives rise
to different encoding challenges in each streaming I/O framework. The
essential challenge here is that to guarantee safe resource
management, these libraries hide the very notion of a stream to the
user. Users cannot directly manipulate streams in arbitrary expressions
of their choosing. Users combine {\em stream processors} (``conduits''
or ``machines'') rather than combining streams directly.

In search of a more flexible framework, Lippmeier \&
al~\cite{lippmeier_parallel_2016} propose an alternative model for
stream processing while attempting to nevertheless offer the same
resource safety guarantees (timely release of resources, no
use-after-free, no free-after-free). In the \verb+repa-flow+ library,
stream processors are just functions, not an abstract type of values
that can only be constructed using a limited vocabulary.

Given a handful of off-the-shelf combinators (which we could as well
have written ourselves since they are not primtives of the framework),
\begin{code}
zipWith_i :: (Flow a, Flow b, Build c)
          => (a -> b -> c) -> Sources a -> Sources b -> IO (Sources c)
connect_i :: Sources a -> IO (Sources a, Sources a)
map_i :: (Flow a, Build b) => (a -> b) -> Sources a -> IO (Sources b)
foldlAllS :: Flow b => (a -> b -> a) -> a -> Sources b -> IO a
dup_io :: Sources a -> Sinks a -> IO (Sources a)
\end{code}
it becomes straightforward to define an example that combines the
features of both the Conduit example and the machines example above:
\begin{code}
interleave3
    :: (Flow a, Build a, Flow b, Build b, Flow c, Build c)
    => Sources a -> Sources b -> Sources c -> IO (Sources (a,(b,c)))
interleave3 sa sb sc = do
    z <- zipWith_i (,) sb sc
    zipWith_i (,) sa z

interleave21
    :: (Flow a, Build a, Flow b, Build b)
    => Sources a -> Sources b -> IO (Sources (a,(b,b)))
interleave21 sa sb = do
    (sb1,sb2) <- connect_i sb
    interleave3 sa sb1 sb2

count :: (Flow a) => Sources a -> IO Int
count s = do
  s' <- map_i (\_->1) s
  foldlSAll (+) 0 s'

-- interleave two input stream and return the length of the stream
interleaveCount
    :: (Flow a, Build a, Flow b, Build b)
     => Sources a -> Sources b -> Sinks (a,(b,b)) -> IO Int
interleaveCount sa sb k = do
  sabb <- interleave21 sa sb
  sabb' <- dup_io sabb k
  count sabb'
\end{code} % $
The catch is that this library is not resource safe. There is nothing
preventing the user from introducing a use-after-free bug. Lippmeier
\& al point out that if only Haskell had linear types (or for that
matter any other means of tracking resources at the type-level), then
a few type signatures in his library could be changed to in fact make
the library resource safe.

In fact, a cornerstone of the Rust programming
language~\cite{matsakis_rust_2014} is that it provides this resource
safety out-of-the-box. Through its borrow checker, Rust captures a
notion of affine types in its type system. The lifetime analysis is
powerful enough to for example ensure that a file handle never escapes
the current lexical scope:

\begin{verbatim}
{
  let path = Path::new("hello.txt");
  let mut file = try!(File::open(&path));
  ... // some code that reads the file
}
// the variable `path` falls out of scope, it cannot exit
// this scope, as part of a closure or otherwise,
// therefore the file can be, and in fact is, closed when
// this scope ends.
\end{verbatim}

The lifetime analysis in Rust makes it possible to remain resource
safe without losing much expressive power at all.

\subsection{Memory management}

Kiselyov \cite{kiselyov_iteratees_2012} argues against fully automatic
resource management for managing I/O resources, such as file
descriptors and buffers. In particular, relying on the garbage
collector to reclaim file descriptors, leads to file descriptor leaks.
In general, the problem with automatic resource management is that the
runtime provides no guarantees as to the timeliness of the resource
reclaiming process. File handle finalizers might run at an arbitrarily
late time in the future. Locks are certainly a bad idea to release
automatically for this reason.

A central tenet of this\unsure{Which one?} paper is,
\begin{center}
\em memory is just a system resource like any other, which, as such,
deserves the parsimonious consumption and timely release that other
resources can.
\end{center}
Fully automatic memory management is certainly convenient, and an
effective means of avoiding use-after-free and free-after-free bugs,
since it is the language runtime that guarantees, via a global dynamic
analysis, that resources are reclaimed only when it is entirely safe
to do so. But this dynamic global analysis is expensive to run. For
this reason, resources are reclaimed in batches, to amortize its cost,
only when resource pressure is deemed to warrant reclaiming those
resources that can be. Worse, this global analysis, aka garbage
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
smaller heap. Indeed many of the above mentioned interactive systems
depend on latency requirements several orders of magnitude lower than
the state of the art garbage collectors are able to sustain.

Whereas GC pauses have frequently been observed to reach 50ms or more
for large heaps of long-lived
objects\footnote{https://blog.pusher.com/latency-working-set-ghc-gc-pick-two/},
games typically target a maximum latency budget of 16ms per rendered
frame, corresponding to a 60 frames per second refresh rate. Whereas
incremental GC's might target single digit millisecond latencies,
often at a substantial cost on throughput, bulk synchronous parallel
programs (see below) synchronize over networks with single digit
microsecond roundtrip latencies.

\subsubsection{Latency matters}

\paragraph{bulk synchronous programming} A very popular model for
applications in high-performance computing is bulk synchronous
parallelism \cite{valiant_bridging_1990}. In this model, computations
are structured as iterating a three step process:
\begin{description}
\item[Compute:] simultaneously start as many threads as there are
  cores in the cluster, each computing over a subset of the data.
\item[Communicate:] all processes communicate results with other nodes
  (e.g. their neighbors in a mesh physics simulation).
\item[Synchronize:] the next iteration does not start until all threads
  synchronize on a global write barrier.
\end{description}
Each iteration is called a ``superstep''. This model is not just the
concern of a small niche: it is comparable to the MapReduce model used
elsewhere, which likewise proceeds in lockstep. The map phase precedes
the shuffle and reduce phases. Mapping again becomes possible once the
previous reduce is complete. A new superstep begins when a previous one
finishes. Even interactive user queries with a total latency envelope
of 100ms can be processed as a sequence of dozens of such parallel
phases.

The reason for introducing a global write barrier is because this
allows {\em one-sided communication}. Traditional message passing
requires synchronization between the sender and the receiver, in
particular to decide on the receiving end where to store the message
in memory (say in some other thread's mailbox). Whereas one-sided
communication is purely asynchronous: writing messages directly at
their final location on the destination node can be coordinated from
the sender, without involving the receiver, and without any
indirection. These asynchronous message sends can be performed across
a cluster in mere microseconds on current hardware. The write barrier
serves to ensure that all one-sided sends are complete before starting
the next iteration.

As we start increasing the number of threads to synchronize on the
global barrier to thousands of threads and beyond, any ``jitter''
(i.e. variance in the thread runtimes) increases the time to fully
reaching the barrier for all threads. Performance crucially depends on
achieving predictable latencies, because the lower the variance, the
tighter we space each barrier in time, and the less threads sit idle
waiting on their peers.

There are of course ways to perform latency hiding. Threads can be
oversubscribed, data can be prefetched, or de-normalized (made
redundant copies of in many locations) and computations duplicated to
reduce the number of neighbours threads have to communicate with.
These solutions all come at a complexity cost in systems that have
often already far exceeded any reasonable complexity budget.
Maintaining low and predictable latencies is therefore a means to
achieve simpler designs.

\paragraph{Stream processing} The Square Kilometer
Array\footnote{https://www.skatelescope.org/} is projected to produce
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

\paragraph{Example 1} Consider the following example, a slight
generalization extracted from a real-world business use case at
Pusher, cited above. The challenge is to maintain a concurrent queue
of messages. Each message can be of arbitrary size, but usually in the
order of kilobytes. There can be many hundreds of thousands of message
to maintain in memory. Old messages are evicted, upon being read by
clients, or if the queue grows too long (so it is okay to lose
messages). Any client can also request for any message in the queue to
be removed. In short, the concurrent queue supports the following
operations:

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

One possible implementation strategy consists in accumulating new
messages into regions holding a fixed number $k$ of messages as they
come in. Once the region is full, we seal the region, push it into the
main GC-managed heap as any odd heap allocated object, and open a new
one.

There are two challenges with this strategy:
\begin{enumerate}
\item While the queue can gainfully be represented as a chain of
  compact regions rather than a chain of messages, the larger the $k$
  value chosen, the more unlikely it is that removing $p$ messages
  from the queue, even consecutive ones, will reclaim any memory.
  compact regions can be rewritten upon deletion of a message, at the
  cost of extra latency. Regions cannot be mutated once sealed, so even
  to mark a message as deleted without bothering to reclaim the memory
  would require maintaining an auxiliary blacklist, which we would need to
  lookup before any read request, at the cost of extra implementation
  complexity. In short, compact regions work great for largely static
  structures parts of which can be considered temporarily immutable
  (and copied when they are not), while in this case the natural
  representation of our queue would be a linked list or tree to allow
  for random deletions.
\item Using compact region to store long-lived data reduces the
  pressure on the \textsc{gc} provided that enough data is stored in
  a compact region. It means that one needs to buffer data before
  compacting it into a self-contained region. There is then a tradeoff
  between GC pressure and extra latency, since |push| becomes an
  $O(k)$ time operation, unless we introduce a background
  opportunistic compaction process.
\end{enumerate}

Note that this example is but one instance of a wide class of similar
use cases, such as in-kernel buffer caches. Our initial use case at
Tweag I/O was an in-memory cache for a distributed on-disk object
storage system. To mask disk access latencies, we hold as many objects
in memory as possible. But to keep the hit rate of the cache high, we
continuously evict old or infreuently used objects to make room for
more recently accessed objects. The objects are mutable. Whenever
a client wants to mutate an object, it needs to {\em lock} the object.
Locking an object requires evicting any copy of the object in any
cache anywhere in the cluster, to maintain consistent read-after-write
and write-after-write semantics. So just like the above example, we
require adding objects to our long-lived object cache, as well as
evicting random objects based on requests from peers in the cluster.

\paragraph{Example 2} Consider the implementation of a low-latency web
server. Typically, a web server maintains no state between requests,
or any state is serialized to some external database on a different
server. That is to say, the state of the heap for the web server
should stay constant. We will need to allocate temporary data structures
to represent the parameters of a request, as well as to assemble
a response. But any allocation in response to a request ought to be
allocated in some stratch space, which is wholly discarded at the end
of each request.

A garbage collector is not needed in such an application: all data
structures are either static or very short-lived. If we avoid it
entirely then it becomes possible to achieve very short and
predictable latencies indeed. Further, it would be nice if we could
{\em guarantee} that the heap will stay constant across requests.

The basic server loop looks like this:

\begin{code}
-- Holds server configuration data
data ServerContext

requestHandler :: Request -> IO Response
  
server :: ServerContext -> IO ()
server cxt = do
  req <- getRequest cxt
  resp <- requestHandler req
  putResponse cxt resp
  server cxt
\end{code}

We could imagine wrapping the call to |requestHandler| with a new
primitive, called

\begin{code}
withRegion :: NFData a => IO a -> IO a
\end{code}

that runs the provided action in the scope of a whole new heap that is
not garbage collected, then makes sure that the given action yields
a fully evaluated value, and finally unilaterally reclaims the scratch
heap in one go. However, a |withRegion| of the above type would be
unsafe! For example, there is nothing stopping the provided action
from stashing a freshly allocated value down a |Chan| to another
thread, hence escaping the dynamic scope of the region.

One tentative solution to this in Haskell is to use monadic regions
\cite{kiselyov_regions_2008}. At a significant syntactic cost: {\em
  all} allocations must then be done explicitly, using specially
provided monadic operators,

\begin{code}
data FileHandle s

newHandle :: FilePath -> RegionIO s (FileHandle s)
readLine :: FileHandle s -> RegionIO s String

runRegion :: (forall s. RegionIO s a) -> IO a
\end{code}

inside a bespoke |ST|-like monad (called |RegionIO| above). Otherwise
pure code now has to be written in a monadic style. Worse, this
approach requires resource specific handle types, with resource
specific projection functions (such as |readLine| above) lifted to
monadic projection actions. The projections are themselves part of the
trusted base, which is ever growing. And nothing guarantees that the
result of projections is allocated in the current region.

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

The type system extension that we propose in a separate document fits
the top two tiers of this hierarchy:
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

\printbibliography

\end{document}
