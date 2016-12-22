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

\author{Jean-Philippe Bernardy, Arnaud Spiwack and Mathieu Boespflug}
\date{\today}
\title{\HaskeLL: A practical lazy language with linear and unrestricted types}
% Linear and unrestricted at the same time
% 
\hypersetup{pdflang={English}}

\begin{document}

\maketitle
%% \tableofcontents
\begin{abstract}
  This article introduces and describes a
  linearly-typed lazy programming language which is designed to be
  integrate well with an existing programming language, in particular
  in GHC/Haskell.
\end{abstract}

\setcounter{tocdepth}{3}
\tableofcontents
\listoffigures

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

\subsection{Options for tracking resources}

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
This style of programming is unsafe. In the above style, there is nothing
preventing the programmer from accidentally reusing the file handle
after calling |hClose|, even though the handle is defunct forever
in the future, or indeed call |hClose| twice. In short, programming
with explicit file handle creation/deletion operators is prone to the
same bugs that plague programming with explicit
allocation/deallocation memory operators.

Strategies to avoid use-after-free and free-after-free
bugs include:

\begin{enumerate}
\item restricting programs to using specifically provided higher-level
  combinators or patterns of programming that reduce their likelihood,
  as in streaming I/O frameworks and the RAII pattern popularized by
  modern C++;
\item making resource disposal implicit and completely automatic via
  a garbage collection (GC) mechanism;
\item using resource-tracking type-systems.
\end{enumerate}

In this paper, we advocate the third option. The next two subsections
review the shortcomings of the first two approaches.

\subsection{Combinator libraries}
Higher-level combinators fall short of enforcing all the resource
management correctness invariants we would like. Further, they impose
a sometimes substantial encoding overhead. While automatic resource
disposal is a problematic source of non-determinism that can be the
cause of subtle performance and/or correctness bugs.

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

\subsection{Automatic memory management}

Kiselyov \cite{kiselyov_iteratees_2012} argues against fully automatic
resource management for managing I/O resources, such as file
descriptors and buffers. In particular, relying on the garbage
collector to reclaim file descriptors, leads to file descriptor leaks.
In general, the problem with automatic resource management is that the
runtime provides no guarantees as to the timeliness of the resource
reclaiming process. File handle finalizers might run at an arbitrarily
late time in the future. Locks are certainly a bad idea to release
automatically for this reason.

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

\subsection{Type-system support}

Type-system for resource management has received a lot of attention in recent
years.  The idea is to forgo automatic management in favor of safe,
but explicit management of resources, including memory. This trend is
best exemplified by the popularity of the Rust programming
language~\cite{matsakis_rust_2014}, where file-reading code such as
what follows would be written\footnote{The Rust compiler has a
  special, so called ``life-time'' analysis, which checks that the
  \texttt{file} is not put in a closure.}:

\begin{verbatim}
{
  let path = Path::new("hello.txt");
  let mut file = try!(File::open(&path));
  // some code that reads the file
} // the file is closed when this scope ends
\end{verbatim}

In particular giving up garbage collection offers the following
benefits:
\begin{itemize}
\item control of \emph{how much} latency is incurred by memory management;
\item control of \emph{when} memory-management pauses occur.
\end{itemize}
Indeed garbage collection is very fast, and explicit memory management
may sometimes be even slower. Yet, fewer and more predictable pauses are
important when operating under real-time constraints or in a
distributed systems: a pause on one process can make all the other
processes wait for the slower process to reach completion.

Languages with safe explicit resource management tend to have vastly
different type systems (such as the ownership and borrowing typing of
Rust). This observation may induce the belief that abandoning the
comfort and convenience of \textsc{ml}-family languages is required to
benefit from the increased safety and control allowed by
garbage-collection free languages.

This article posits that, to the contrary, existing programming
languages, such as Haskell~\cite{marlow_haskell_2010}, can be extended
to incorporate safe explicit resource management, and gain a measure
of control on garbage-collection pauses. Taking cues from linear
logic~(LL)~\cite{girard_linear_1987}, we propose a linearly typed
lazy\footnote{Laziness is not an essential characteristic: a similar
  extension can be designed for a strict language. Yet the
  presentation in this article is inherently lazy: both the static and
  dynamic semantics would change slightly in a strict language} lambda
calculus (inspired by \textcite{mcbride_rig_2016} and \textcite{ghica_bounded_2014}),
which contains the simply-typed lambda calculus as a subset.

This lambda calculus can be scaled up to a full-fledged programming
language and is itself a conservative extension of Haskell. Thus we
(cheekily) call it \HaskeLL.
Concretely, in \HaskeLL,
one enjoys the convenience of programming in Haskell;
but when part of code requires more care, \emph{e.g.} because of
efficiency (sections~\ref{sec:fusion} and \ref{sec:dynamics}), or
because a foreign function needs a linear type
(Section~\ref{sec:ffi}), then one can use seamlessly the linear
features of the language, which allow more control.

For example, one may ensure that file handles do not remain dangling
by giving the following type to a file-accessing functions:
\begin{code}
  withFile :: FilePath -> (Handle ⊸ IO (Bang a)) ⊸ IO a
  hClose :: Handle ⊸ IO ()
\end{code}
Given this primitive, the running example becomes\footnote{see
  \fref{sec:resources} for a detailed discussion of this example}:
\begin{code}
withFile "myfile" ReadMore $ \h -> do
    -- some code that reads the file
    hClose h
    return (Bang ()) -- Ensures that there is no linear resource left
\end{code}
% Add a dollar to prevent syntax highlighting to go wild: $

A type system based on linear logic is considerably simpler than one
based on uniqueness or ownership. Additionally, it makes it possible
to leverage the wealth of literature of the past thirty years. Linear
logic has been shown, for instance, to be applicable to explicit
memory
management~\cite{lafont_linear_1988,hofmann_in-place_,ahmed_l3_2007},
memory-efficient array computations through
fusion~\cite{bernardy_duality_2015,lippmeier_parallel_2016}, protocol
specification (as session types)~\cite{honda_session_1993} (the
correspondence between session types and linear types is explained
in~\cite{wadler_propositions_2012}), privacy
guarantees\cite{gaboardi_linear_2013}, and graphical
interfaces\cite{krishnaswami_gui_2011}.


\section{A taste of \HaskeLL}
\label{sec:programming-intro}
The latter are
extensionally equivalent to regular functions but are guaranteed to
consume their argument exactly once. To be precise, the arrow type is
parametrized by the amount (hereafter referred to as the weight) of
its argument that it requires:

We propose a programming language with two arrow types: one for usual
intuitionistic functions, and one for linear functions. The are a
subset of the former: they are functions which guarantee to consume
exactly once their argument. To be precise, we propose a
generalisation, where the arrow type is parametrized by the amount of
its argument that it requires (exactly once or any number of times):
\begin{itemize}
\item $A →_1 B$ is the linear arrow $A ⊸ B$
\item $A →_ω B$ is the usual intuitionistic arrow $A → B$
\end{itemize}

The first main benefit of this approach is that all the code already
written, assuming an $ω$-sized supply of everything, can work out of
the box.

The second benefit is that one can write linear code whenever it is
possible, and use it in unrestricted contexts anyway. The following
example illustrates. (Note that all top-level bindings, including
constructors and class methods are assumed to have weight $ω$, unless
explicitly specified otherwise.)

\begin{code}
data List a where
  [] :: List a
  (:) :: a ⊸ List a ⊸ List a
\end{code}


The above data declaration defines a linear version of the list
type.

That is, given \emph{one} instance of a list, one will obtain
\emph{exactly one} instance of each of the items contained inside it.
Thus the above list may contain (handles to) resources without
compromising safety.

Many list-based functions conserve the quantity of data, and thus can
be given a more precise type. For example we can write |(++)|
as follows:

\begin{code}
(++) :: List a ⊸ List a ⊸ List a
[]      ++ ys = ys
(x:xs)  ++ ys = x : (xs ++ ys)
\end{code}

The type of |(++)| tells us that if we have quantity $1$ of
a list |xs|, appending any other list to it will never duplicate any
of the elements in |xs|, nor drop any element in |xs|. Note that in
our system, giving a more precise type to |(++)| strengthens the
contract that the implementation of |(++)| must satisfy, but it
doesn't restrict its usage. It is perfectly legal to provide an $ω$
quantity |xs| as an argument, or indeed to {\em promote} the result of
the function, of quantity $1$, to quantity $ω$. The intuition is that, in
a context that wants zero or more of a resource, providing exactly one
of that resource will do.
Concretely if one has a quantity $ω$ for both inputs, one can
call $ω$ times |(++)| to obtain $ω$ times the concatenation.

\begin{aside}
Those with an operational background may want to think of a linear
list (one with weight 1) as one that a does not need to live
on a \textsc{gc}'ed heap\footnote{even though it can} --- instead it
can be put on an explicitly managed heap (which we call the linear
heap in what follows). If so, that list can thus be deallocated
exactly at the point of its consumption. In a lazy language, the
thunks on the linear heap can even free themselves.

The operational interpretation of promotion of linear to unrestricted
is as follows: one can linear code in a special mode which allocates
on the GC heap instead of the linear heap.
\end{aside}


Of course, not all programs are linear: a function may legitimately
demand $ω$ times its input, even to construct a single output. For
example the function repeating indefinitely its input will have the
type:
\begin{code}
cycle :: List a → List a
\end{code}
Operationally, |cycle| requires its argument to be on the \textsc{gc} heap.  In
practice, libraries will never provide $ω$ times a scarce resource
(e.g. a handle to a physical entity); such a resource will thus never
end up in the argument to |cycle|.

While reusing first-order code can be done simply by scaling from $1$
to $ω$, reusing higher-order programs need polymorphism over
weights. For example, the standard |map| function
\begin{code}
map f []      = []
map f (x:xs)  = f x : map f xs
\end{code}
can be given the two incomparable following types: |(a ⊸ b) -> List a
⊸ List b| and |(a -> b) -> List a -> List b|. The type subsuming both versions is
|∀ρ. (a -> _ ρ b) -> List a -> _ ρ List b|. 
%
Likewise, function composition can be given the following type:
\begin{code}
(∘) :: forall π ρ. (b → _ π c) ⊸ (a → _ ρ b) → _ π a → _ (ρ π) c
(f ∘ g) x = f (g x)
\end{code}
What the above type says is that two functions of arbitrary linearities $ρ$
and $π$ can be combined into a function of linearity $ρπ$.

One might be tempted to mark all constructor types as linear, i.e.
with only |⊸|-arrows in their types, in the style of the |List| type
above. After all, linear constructors, like any linear function, are
happy to be provided resources of any quantity. However, $ω$-weighted
arrows in constructors are useful too, as the following data type
illustrates\footnote{The type constructor |Bang| is in fact an
  encoding of the so-called \emph{exponential} modality written ${!}$
  in linear logic.}:
\begin{code}
  data Bang a where
    Bang :: a → Bang a
\end{code}
It is used to indicate that a linear function returns $ω$-weighted
results. For example:
\begin{code}
  copy :: Bool ⊸ Bang Bool
  copy True = Bang True
  copy False = Bang False
\end{code}
We stress that the above is not the same as the linear identity
function, |id :: Bool ⊸ Bool|. Indeed, |id| conserves the weight of
|Bool|, whereas |copy| \emph{always} returns an $ω$-weighted value,
regardless of the weight of its argument.

We won't detail here the formal static semantics for the entire
language, but here are a few intuitive rules:
\begin{enumerate}
\item A linear ($1$ quantity) value {\bf can} be passed to a linear
  function.
\item A regular ($ω$ quantity) value {\bf can} be passed to a linear
  function.
\item A linear value {\bf cannot} be passed to a regular function.
\item A regular value {\bf can} be passed to a regular function.
\item A linear value {\bf can} be returned by a linear function.
\item A regular value {\bf can} be returned by a linear function.
\item A linear value {\bf can} be returned by a regular function (but
  it will be promoted to a regular value in so doing).
\item A regular value {\bf can} be returned by a regular function.
\end{enumerate}

In code, this means that |g| below admits the following
implementations, but not the last one:
\begin{code}
f :: a ⊸ a
g :: (Int ⊸ Int -> r) -> Int ⊸ Int -> r

g k x y = k (f x) y      -- Good
g k x y = k x (f y)      -- Good
g k x y = k x y          -- Good
g k x y = k y x          -- Bad
\end{code}

\paragraph{A GC-less queue API}

With linear types, it's possible to write a {\em pure} and {\em
  memory-safe} API for managing foreign C data. Indeed, since linear
data must be used \emph{exactly once}, it means that such data is
statically guaranteed to eventually be consumed by the program (no
unfreed garbage) and that the data cannot be referred to after being
consumed (freedom from use-after-free or free-after-free bugs).

Concretely, such an API is defined in an ownership-passing
fashion: operations that do not free the data structure return a new
copy of the data structure (which may be the same as the original).
For instance, pushing in a queue would have the following type:
\begin{code}
push :: Msg -> Queue ⊸ Queue
\end{code}
While functions to free the data structure would simply consume the
argument as follows:
\begin{code}
free :: Queue ⊸ ()
\end{code}

This makes it possible to statically manage long-lived data without
adding to GC pressure, since the data lives in a foreign heap.
A complete API for queues with random access deletion could
be typed as follows (|Msg| must be |Storable| to (un)marshall values
to/from the regular GC'ed heap):
\begin{code}
instance Storable Msg

alloc   :: (Queue ⊸ Bang a) ⊸ a
free    :: Queue ⊸ ()

push    :: Msg -> Queue ⊸ Queue
delete  :: Msg -> Queue ⊸ Queue
evict   :: Int -> Queue ⊸ (Queue, Bang (Vector Msg))
\end{code}
There are a few things going on in this API:
\begin{itemize}
\item |alloc| opens a new scope, delimited by the dynamic extent of
  its argument function. This function is provided a fresh queue,
  allocated in the foreign heap (for example using \verb|malloc()|).
  This queue must be used exactly once. The return type of argument
  function is |Bang a|, ensuring that no linear value can be returned:
  in particular the |Queue| must be consumed.
\item Messages of type |Msg| are copied into regular Haskell values
  (hence managed by the garbage collector) when they are returned by
  |evict|. The hypothesis is that while there is a very large amount
  of messages in the queue, there will at any given time be very few
  messages managed by the garbage collector. Since these objects will
  typically be short-lived, they won't normally survive a ``generation
  0'' sweep.
\item Because the queue allocated by |alloc| must be consumed before
  reaching the end of the scope, |free| must be called. Indeed, there
  is no other way to properly get rid of the queue. Calling any of the
  other linear functions does ``consume'' the queue, but returns a new
  one, along with the obligation of getting rid of that one!
\end{itemize}

\todo{Probably add a remark that functional in-place update is not a goal... But it works though.}

\section{\calc{} statics}
In this section we concentrate on the calculus at the core of
\HaskeLL{}, namely \calc{}, and give a step by step account of its
syntax and typing rules.
\subsection{Typing contexts}
\label{sec:typing-contexts}

In \calc{}, each variable in typing contexts is annotated with the number of times
that the program must use the variable in question. We call this
number of times the \emph{weight} of the variable.

Concrete weights are either $1$ or $ω$: when the weight is $1$, the program
\emph{must} consume the variable exactly once; when the weight is $ω$,
it \emph{may} consume it any number of times (possibly zero). For the
sake of polymorphism, weights are extended with weight
\emph{expressions}, which contain variables (ranged over by the
metasyntactic variables \(π\) and \(ρ\)), sum, and product. The
complete syntax of weights and contexts can be found in
\fref{fig:contexts}.

In addition, weights are equipped with an equivalence relation $(=)$
which obeys the following laws:

\begin{itemize}
\item $+$ and $·$ are associative and commutative
\item $1$ is the unit of $·$
\item $·$ distributes over $+$
\item $ω · ω = ω$
\item $1 + ω = ω$
\item $1 + 1 = ω$
\item $ω + ω = ω$
\end{itemize}
Thus, weights form a semi-ring (without a zero), which extends to a
module structure on typing contexts as follows.

\begin{definition}[Context addition]~
  \begin{align*}
    (x :_p A,Γ) + (x :_q A,Δ) &= x :_{p+q} A, (Γ+Δ)\\
    (x :_p A,Γ) + Δ &= x :_p A, Γ+Δ & (x ∉ Δ)\\
    () + Δ &= Δ
  \end{align*}
\end{definition}

\begin{definition}[Context scaling]
  \begin{displaymath}
    p(x :_q A, Γ) =  x :_{pq} A, pΓ
  \end{displaymath}
\end{definition}

\begin{lemma}[Contexts form a module]
  The following laws hold:
  \begin{align*}
    Γ + Δ &= Δ + Γ\\
    p (Γ+Δ) &= p Γ + p Δ\\
    (p+q) Γ &= p Γ+ q Γ \\
    (pq) Γ &= p (q Γ)\\
    1 Γ &= Γ
  \end{align*}
\end{lemma}

\subsection{Typing}

The static semantics of \calc{} is expressed in terms of the
familiar-looking judgement \(Γ ⊢ t : A\). The meaning of this
judgement, however, may be less familiar. Indeed, remember that $Γ$ is
weight-annotated, the weight of a variable denoting the quantity of
that variable available in $Γ$. The judgement \(Γ ⊢ t : A\) ought to
be read as follows: the term $t$ consumes $Γ$ and builds \emph{exactly
  one} $A$. This section defines the judgement \(Γ ⊢ t : A\).

\begin{figure}
  \figuresection{Weights}
  \begin{align*}
    p,q &::= 1 ~||~ ω ~||~ π ~||~ p+q ~||~ p·q
  \end{align*}
  \figuresection{Contexts}
  \begin{align*}
    Γ,Δ & ::=\\
        & ||  x :_q A, Γ & \text{weight-annotated binder} \\
        & ||     & \text {empty context}
  \end{align*}

  \figuresection{Type declarations}
  \begin{align*}
    \data D  \mathsf{where} \left(c_k : A₁ →_{q₁} ⋯    A_{n_k} →_{q_{n_k}} D\right)^m_{k=1}
  \end{align*}

  \figuresection{Types}
  \begin{align*}
  A,B &::=\\
      & ||  A →_q B &\text{function type}\\
      & ||  ∀ρ. A &\text{weight-dependent type}\\
      & ||  D &\text{data type}
  \end{align*}

  \figuresection{Terms}
  \begin{align*}
    e,s,t,u & ::= \\
            & ||  x & \text{variable} \\
            & ||  λ(x:_qA). t & \text{abstraction} \\
            & ||  t_q s & \text{application} \\
            & ||  λπ. t & \text{weight abstraction} \\
            & ||  t p & \text{weight application} \\
            & ||  c t₁ … t_n & \text{data construction} \\
            & ||  \case[p] t {c_k  x₁ … x_{n_k} → u_k}  & \text{case} \\
            & ||  \flet x_1 :_{q₁}A₁ = t₁ … x_n :_{q_n}A_n = t_n \fin u & \text{let}
  \end{align*}

  \caption{Syntax of the linear calculus}
  \label{fig:syntax}
  \label{fig:contexts}
\end{figure}

The types of \calc{} (see \fref{fig:syntax}) are simple
types with arrows (albeit weighted ones), data types, and weight
polymorphism.  The weighted function type is a generalization of the
intuitionistic arrow and the linear arrow. We will use the following
notations:
\begin{itemize}
\item \(A → B ≝  A →_ω B\)
\item \(A ⊸ B ≝ A →_1 B\)
\end{itemize}
The intuition behind the weighted arrow \(A →_q B\) is that you can
get a \(B\) if you can provide a quantity \(q\) of \(A\). Note in
particular that when one has $x :_ω A$ and $f :_1 A ⊸ B$, the call
$f x$ is well-typed. Therefore, the constraints imposed by weights on
arrow types is dual to those they impose on variables in the context:
a function of type $A→B$ \emph{must} be applied to an argument of
weight $ω$, while a function of type $A⊸B$ \emph{may} be applied to an
argument of weight $1$ or $ω$.
  Thus one may expect the type $A⊸B$ to be a subtype of $A→B$, however
  we chose not to provide subtyping, for the sake of simplicity.
  \begin{aside}
    One can systematically promote linear functions thus:
    \begin{code}
      promote :: (A ⊸ B) ⊸ (A → B)
      promote f x = f x
    \end{code}
    So a programmer shall prefer to provide a linear function (and
    conversely accept unrestricted functions), all other
    considerations being equal.
  \end{aside}



  Data type declarations, also presented in \fref{fig:syntax},
  deserve some additional explanation.
  \begin{align*}
    \data D  \mathsf{where} \left(c_k : A₁ →_{q₁} ⋯    A_{n_k} →_{q_{n_k}} D\right)^m_{k=1}
  \end{align*}
  The above declaration means that \(D\) has \(m\) constructors \(c_k\), for \(k ∈ 1…m\),
  each with \(n_k\) arguments. Arguments of constructors have a
  weight, just like arguments of function: an argument of weight $ω$
  means that the data type can store, at that position, data which
  \emph{must} have weight $ω$; while a weight of $1$ means that data
  at that position \emph{can} have weight $1$ (or $ω$). A further
  requirement is that the weights $q_i$ will either be $1$ or
  $ω$.\info{The requirement that weights are constant in constructor
    makes sense in the dynamic semantics, it's not only to simplify
    the presentation with consideration about type polymorphism. There
    may be a meaning to weight-polymorphic data type, but I [aspiwack]
    can't see it.}\unsure{Should we explain some of the above in the
    text?}

  For most purposes, $c_k$ behaves like a constant with the type
  $A₁ →_{q₁} ⋯ A_{n_k} →_{q_{n_k}} D$. As the typing rules of
  \fref{fig:typing} make clear, this means in particular
  that to have a quantity $ω$ of data of type $D$, all its sub-data
  including the arguments declared with weight $1$ must have weight
  $ω$. Conversely, given $ω$ times all the arguments of $c_k$, one can
  construct a quantity $ω$ of $D$.

  Note that constructors with arguments of weight $1$ are not more
  general than constructors with arguments of weight $ω$, because if,
  when constructing $c u$, with the argument of $c$ of weight $1$, $u$
  \emph{may} be either of weight $1$ or of weight $ω$, dually, when
  pattern-matching on $c x$, $x$ \emph{must} be of weight $1$ (if the
  argument of $c$ had been of weight $ω$, on the other hand, then $x$
  could be used either as having weight $ω$ or $1$).

The following example of data-type declarations illustrate the role of
weights in constructor arguments:
\begin{itemize}
\item The type
  $\data \varid{Pair} A B \where \varid{Pair} : A →_ω B →_ω
  \varid{Pair} A B$ is the intuitionistic product (usually written
  $A×B$)
\item The type
  $\data \varid{Tensor} A B \where \varid{Tensor} : A →_1 B →_1
  \varid{Tensor} A B$ is the linear tensor product (usually written
  $A⊗B$)
\item The type
  $\data \varid{Bang} A \where \varid{Bang} : A→_ω \varid{Bang} A$ is
  the exponential modality of linear logic (usually written ${!}A$)
\end{itemize}

The term syntax (\fref{fig:syntax}) is that of a
type-annotated (\textit{à la} Church) simply typed $λ$-calculus
with let-definitions. Binders in $λ$-abstractions and type definitions
are annotated with both their type and their weight (echoing the
typing context from Section~\ref{sec:typing-contexts}). Weight
abstraction and application are explicit.

It is perhaps more surprising that applications and cases are
annotated by a weight. This information is usually redundant, but we
use it in Section~\ref{sec:dynamics} to define a compositional
dynamic semantics with prompt deallocation of data. We sometimes omit
the weights or type annotations when they are obvious from the
context, especially in the case of applications.

%%% typing rule macros %%%
\newcommand{\apprule}{\inferrule{Γ ⊢ t :  A →_q B  \\   Δ ⊢ u : A}{Γ+qΔ ⊢ t_q u  :  B}\text{app}}
\newcommand{\varrule}{\inferrule{ }{ωΓ + x :_1 A ⊢ x : A}\text{var}}
\newcommand{\caserule}{\inferrule{Γ   ⊢  t  : D  \\ Δ, x₁:_{pqᵢ} Aᵢ, …,
      x_{n_k}:_{pq_{n_k}} A_{n_k} ⊢ u_k : C \\
      \text{for each $c_k : A_1 →_{q_1} … →_{q_{n-1}} A_{n_k} →_{q_{n_k}} D$}}
    {pΓ+Δ ⊢ \case[p] t {c_k  x₁ … x_{n_k} → u_k} : C}\text{case}}
%%% /macros %%%

\begin{figure}
  \begin{mathpar}
    \varrule

    \inferrule{Γ, x :_{q} A  ⊢   t : B}
    {Γ ⊢ λ(x:_q A). t  :  A  →_q  B}\text{abs}

    \apprule

    \inferrule{Δᵢ ⊢ tᵢ : Aᵢ \\ \text {$c_k : A_1 →_{q_1} … →_{q_{n-1}}
        A_n →_{q_n} D$ constructor}}
    {\sum_i qᵢΔᵢ ⊢ c_k  t₁ … t_n :  D}\text{con}

    \caserule

    \inferrule{Γᵢ   ⊢  tᵢ  : Aᵢ  \\ Δ, x₁:_{q₁} A₁ …  x_n:_{q_{n}} A_n ⊢ u : C }
    { Δ+\sum_i qᵢΓᵢ ⊢ \flet x_1 :_{q₁}A_1 = t₁  …  x_n :_{q_n}A_n = t_n  \fin u : C}\text{let}

    \inferrule{Γ ⊢  t : A \\ \text {$π$ fresh for $Γ$}}
    {Γ ⊢ λπ. t : ∀π. A}\text{w.abs}

    \inferrule{Γ ⊢ t :  ∀π. A}
    {Γ ⊢ t p  :  A[p/π]}\text{w.app}
  \end{mathpar}

  \caption{Typing rules}
  \label{fig:typing}
\end{figure}

\improvement{It may be useful to have a better transition between
  syntax and typing judgement}

Remember that the typing judgement \(Γ ⊢ t : A\) reads as: the term $t$ consumes $Γ$ and
builds \emph{exactly one} $A$.
This is the only kind of judgement in \calc{}: we provide
no judgement to mean ``the term $t$ consumes $Γ$ and builds a quantity $p$ of $ A$-s''. Instead, we
make use of context scaling: if \(Γ ⊢ t : A\) holds, then from \(pΓ\)
one builds a quantity $p$ of $A$, using the same term $t$. This idea is at play in the
application rule (the complete set of rules can be found in
\fref{fig:typing}):
$$\apprule$$
Here, $t$ requires its argument $u$ to have weight $q$. Thus $Δ ⊢ u : A$
give us $u$ with a weight of $1$, and therefore the application needs $qΔ$
to have a quantity $q$ of $u$ at its disposal. This rule is the flip side
of the weighted arrows which allow to have the $λ$-calculus
as a subset of \calc{}:\improvement{maybe work a little on the presentation of this
  example}
$$
\inferrule
{\inferrule
  {\inferrule
    {\inferrule{ }{x :_ω A ⊢ x : A}\text{var} \qquad \inferrule{ }{x :_ω A ⊢ x : A}\text{var}}
    {x :_ω A ⊢ Tensor x x : Tensor A A}\text{con}}
  {⊢ λ (x :_ω A). Tensor x x : A →_ω Tensor A A}\text{abs} \qquad \inferrule{\vdots}{⊢ id_ω 42 : A}}
{()+ω() ⊢ (λ (x :_ω A). Tensor x x)_ω \; (id_ω \; 42)}\text{app}
$$
\begin{aside}
In the application rule the promotion rule of linear logic is applied
implicitly.
$$\inferrule{{!}Γ ⊢ A}{{!}Γ ⊢ {!}A}$$
where ${!}Γ$ is a context with all the hypotheses of the form ${!}A$
for some $A$. See \fref{sec:ill} for further comparison.
\end{aside}
This implicit use of the promotion rule is what makes it possible to
seamlessly mix linear types and intuitionistic types inside the same
language. The whole idea is a bit subtle, and it may be worth it to
ponder for a moment why it works as advertised.  \info{There is a
  presentation of the application which is closer to the usual
  promotion rule: requiring $\Delta$ to be divisible by $q$ (and not
  scale $\Delta$ in the conclusion). This works fine when weights are
  $1$ and $\omega$, but will fail with $0$ (used for uniform
  quantification in a dependently typed presentation) or more exotic
  weights (such as $2$).}  \unsure{Should we make a comment explaining
  the above?}

The variable rule, used in the above example, may require some
clarification.
$$\varrule$$
The variable rule is the rule which implements the weakening of
$ω$-weighted variables: that is, it allows ignoring variables of weight
$ω$. \footnote{Pushing weakening to
the variable rule is classic in many lambda calculi, and in the case
of linear logic, dates back at least to Andreoli's work on
focusing~\cite{andreoli_logic_1992}.} Note that the judgement
$x :_ω A ⊢ x : A$ is an instance of the variable rule, because
$(x :_ω A)+(x :_1 A) = x:_ω A$.

Most of the other typing rules are straightforward, but let us linger
for a moment on the case rule:
$$\caserule$$
Like the application rule it is parametrized by a weight $p$. But,
while in the application rule only the argument is affected by $p$, in
the case rule, not only the scrutinee but also the variable bindings
in the branches are affected by $p$. What it means, concretely, is
that the weight of data is \emph{inherited} by its sub-data: if we
have a quantity $1$ of $A⊗B$ we have a quantity $1$ of $A$ and a
quantity $1$ of $B$, and if we have a quantity $ω$ of $A⊗B$ we have a
quantity $ω$ of $A$ and a quantity $ω$ of $B$. Therefore, the
following program, which asserts the existence of projections, is
well-typed (note that, both in |first| and |snd|, the arrow is~---~and
must be~---~non-linear)
\begin{code}
  data (⊗) a b where
    (,) : a ⊸ b ⊸ a⊗b

  first  :: a⊗b → a
  first (a,b)  = a

  snd  :: a⊗b → b
  snd (a,b)  = b
\end{code}
\begin{aside}
These projections exhibit a small deviation from linear logic: the
existence of these projections mean that ${!}(A⊗B)$ is isomorphic to
${!}({!}A⊗{!}B)$. While this additional law may restrict the
applicable models of \calc{} (hence may be inconvenient for some
applications), it is key to retro-fitting linearity in an existing
language: if we interpret the weights on the arguments of existing
constructor to be $1$ while the weights on the arguments of existing
functions to be $ω$, the typable programs are exactly the same as an
intuitionistic $λ$-calculus.
\end{aside}
\info{Remark: the reason why we can have
  ${!}(A\otimes B) \simeq {!}({!}A\otimes{!}B)$ is that we have a
  model in mind where all sub-data is boxed (and managed by \textsc{gc}) if the
  data is managed by \textsc{gc}. In a model where sub-data is unboxed, we
  would need the ability to copy sub-data (\emph{chunks of data}) into
  the \textsc{gc}-ed heap, which is not necessarily available for all data. So
  this extension of linear logic fits our Haskellian model rather
  snugly. (Attn: it will not work for weight 0 though!). It is not the
  only possible path, however.}

\subsection{Examples of simple programs and their types}
\unsure{Scrap this section?}
In order to assess the power of \calc{}, let us consider a few
simple programs and the types that they inhabit.

\paragraph{K combinator}

The $\lambda$-calculus expression $k ≝ λx. λy. x$ can be elaborated
\calc{} to have either the type $A ⊸ B → A$ or $A → B → A$. However,
using the first type does not restrict the programs one can write,
because when we heave $ω$ times $A$, we can always call $k$ anyway and
ignore the rest of $A$'s. (In this situation, we can also call $ω$
times $k$). The lesson learned is that when a variable is used
(syntactically) just once, it is better to give it the weight
1.\info{In our system we could also give the type $∀ π. A →_π B → A$,
  because $π$ can range only over $1$ or $ω$. It would always better
  to use $⊸$ if there were a subtyping relation; but now we may have
  to $\eta$-expand $k$ sometimes.}

\paragraph{Second order Identity}

Similarly $a ≝ λf.λx.f x$ could inhabit all the following types:
$(A → B) → A → B$,
$(A → B) ⊸ A → B$ and
$(A ⊸ B) ⊸ A ⊸ B$.

As per the lesson learned in the previous paragraph, the first type is
dominated by the second one. However the remaining two types are
incomparable. If we want to find a most general type we need to
abstract over the weight of $A$:
\[ λρ. λf. λx. f x : (A →_ρ B) → A →_ρ B.\]

\paragraph{Function composition}
The need for weight abstraction typically occurs in all higher order
functions.  In particular, function composition inhabits a wealth of
incomparable weight-monomorphic types. Yet they can subsumed by
abstracting over the linearities of the input functions, as follows:

\[ λπ. λρ. λf. λg. λx. f (g x) : (B →_π C) ⊸ (A →_ρ B) →_π A →_{πρ} C\]

\paragraph{Ill-typed programs}

As most type systems, \calc{} is perhaps better understood by the
programs it rejects than the programs it accepts. Linear types add
three brands of type errors, let us illustrate all three with three
stripped-down \HaskeLL{} examples, each being the bare minimum to
exhibit one kind of type-checking failure. A program can fail because
it uses a linear variable several time on a code path:
\begin{code}
  data (⊗) a b where
    (,) :: a ⊸ b ⊸ a⊗b

  dup :: a ⊸ a⊗a
  dup x = (x,x)
\end{code}
\begin{quote}\color{red}
  Variable `x' is used, while it has been exhausted\\
  In the expression: |x|\\
  In the expression: |(x,x)|
\end{quote}
The second cause of type-checking failure is similar, except that it
concerns expressions rather than variables. When an expression of
weight $1$ where weight $ω$ is required:
\begin{code}
  unrestricted :: a -> a
  unrestricted x = x

  restriction :: a ⊸ a
  restriction x = unrestricted (x,True)
\end{code}
\begin{quote}\color{red}
  Couldn't match expected weight `$ω$' with actual weight `1'\\
  In the expression: |(x,True)|\\
  In the expression: unrestricted |(x,True)|
\end{quote}
Finally, and dually, it is an error to forget to use a linear
variable:
\begin{code}
  drop :: a ⊸ ()
  drop x = ()
\end{code}
\begin{quote}\color{red}
  Variable `x' is unused, while it has weight `1'\\
  In the expression: |()|
\end{quote}
\improvement{Maybe a slightly more complex program with a |case|
  expression to illustrate that each code path (branch) must have a single use
  of linear variables?}

\section{Applications}
\label{sec:app}

\subsection{Protocols}
\label{sec:protocols}

Linear types as proposed here can be conveniently used to represent
protocols. When used for this purpose, the negation of types becomes
an important construction, because it corresponds to taking the point
of view of the other party. Linear logic typically features a bottom
type $⊥$, whose computational interpretation is that of a terminating
computation. Given this type, $A ⊸ ⊥$ is an adequate representation
for the negation of $A$.
\begin{code}
type Dual a = a ⊸ ⊥
\end{code}
Many languages with session types offer duality at their core, and
conveniently make negation involutive (|Dual (Dual a) = a|). We neither rely on nor provide
this feature: it is not essential to precisely and concisely describe
protocols.  Additionally, we propose no primitive $⊥$ type for
\HaskeLL{}: instead we assume an abstract type $⊥$, typically provided
by a library together with a combinator which executes the embedded
computation:
\begin{code}
type ⊥ -- abstract
runComputation :: ⊥ ⊸ IO ()
\end{code}
Assuming the above signature, we can for example define a protocol for a simple
`bank-account' server. We do so by simultaneously defining two dual types,
corresponding to either the point of view of the server or the client.
\begin{code}
data Status = Success | Failure
data Client where
  Deposit  :: Nat -> Dual Server ⊸ Client
  Withdraw :: Nat -> Dual (Status ⊗ Server) ⊸ Client
type Server = Dual Client
\end{code}

The |Client| type describes the possible behaviors of the
client. When it |Deposit|s, it provides a certain amount and a means
to get a response from the server (|Dual Server|). Upon |Withdraw|al, the
response will additionally indicate if withdrawal was successful.

For good measure, we can show how to implement a simple server which
satisfies the protocol:
\begin{code}
server :: Nat -> Server
server balance client = case client of
  Deposit amount respond  -> respond (server (balance + amount))
  Withdraw amount respond
    | amount >= balance   -> respond (Success, server (balance - amount))
    | otherwise           -> respond (Failure, server balance)
\end{code}

The linearity of client/server states ensures that:
\begin{enumerate}
\item The protocol is respected. This is crucial in a real
  implementation, because the effects that inevitably come into play
  (database, logging, etc. ...) are neither lost nor duplicated. In
  such a situation, the effect will be embedded in the $⊥$ type.
\item The implementation will not `hold onto' any stale client or
  state any longer than strictly necessary: no memory leak can occur.
\end{enumerate}

\subsection{Resources}
\label{sec:resources}
One potential approach to resource management is to put one server in
charge of it. The protocol can be encoded using linear types, as
explained in the previous section. Concretely, the API may look as
follows:
\begin{code}
data IOClient where
  OpenFile  :: FilePath -> Dual (Handle ⊗ IOServer) ⊸ IOClient
\end{code}

A problem with the above API is that the above requires rewriting all
IO code around this idea. One may instead piggyback on the existing
|IO| monad. A possible API for file opening may be:
\begin{code}
withFile :: FilePath -> (Handle ⊸ IO (Bang a)) ⊸ IO a
\end{code}
Given the above type, the handle must be consumed exactly once by the
continuation, and because |Handle| is an abstract type, the user code
cannot discard nor duplicate handles. The API demands that the
continuation returns a |Bang| type, because the continuation should be
called once per call to |withFile|, but the in-IO result of |withFile|
(of type |a|) can be shared. A consequence of returning |Bang| is that
it is impossible to put the |Handle| inside the result\footnote{Thus the
  general linearity check subsumes ``life-time analysis'' a-la Rust.}. This
restriction is the first advantage of the above function compared to,
say, |withFile :: FilePath → (Handle → IO a) → IO a|. Namely, the
static scope of a handle is guaranteed to match its dynamic scope.

The second advantage is is that the |Handle| can be closed \emph{at
  any point} within the continuation (not just at the end --- we show
an example in \fref{fig:lin-IO}). However, to take advantage of this
feature, one must change the type of the monadic bind for IO. Indeed,
consider the Haskell type for bind:
\begin{code}
(>>=) :: IO a → (a → IO b) → IO b
\end{code}
If one were to call |hClose handle| within either of the arguments of
|(>>=)|, the type system would require |handle :: _ ω Handle|,
because the arguments of |(>>=)| carry the $ω$ weight. A way to escape
this problem is to change the type of |(>>=)|. Such a change is
fortunately possible because |IO| guarantees that the arguments of
|(>>=)| are called exactly once (we say that |IO| is a linear
monad). Thus we may have the type:
\begin{code}
(>>=) :: IO (Bang a) ⊸ (a → IO b) ⊸ IO b
\end{code}
The above type is as such not very convenient as it requires the first
argument to systematically return a |Bang| type. We can however embed
the multiplicity of the payload as an argument to |IO|.  An action of
type |IO 1 a| returns a linear payload, while one of type |IO ω a|
returns a shareable payload. Thus the second argument of bind may use
as many times its argument as the first argument embeds.
\begin{code}
return :: a → _ ρ IO ρ a
(>>=) :: ∀ π. IO π a ⊸ (a → _ ρ IO b) ⊸ IO π b
\end{code}
Given such an interface, one can type |openFile| in direct style,
thus:
\begin{code}
openFile :: FilePath ⊸ IO 1 Handle
\end{code}
User code may then look like the example of \fref{fig:lin-IO}.
\begin{figure}
  \centering
  \begin{code}
  example = do
    h1 <- openFile "file1"
    -- h1 in scope
    h2 <- openFile "file2"
    -- h1 and h2 in scope
    hClose h1
    -- h2 in scope
    hClose h2
    -- no handle in scope
  \end{code}
  \caption{Example of code with linear IO}
  \label{fig:lin-IO}
\end{figure}

Not all monads are linear though, so one may want to generalize in
this direction as well. One way to generalise linear and non-linear
monads is to make the 1st-order linearity of |(>>=)| a function of the
monadic type, as \textcite{morris_best_2016} does:
\begin{code}
class Monad q m | m -> q where
  return :: a → m a
  (>>=) :: m a → _ q (a → m b) → _ q m b
\end{code}
Generalizing in both directions yields:
\begin{code}
class Monad q m | m -> q where
  return :: a → _ r m r a
  (>>=) :: m r a → _ (q) (a → _ (r) m r' b) → _ q m r' b
\end{code}
Let us count: bind calls its second argument |q| times, and it itself
needs its argument |r| times. So, the first argument of bind needs to
produce |qr| times |a|. We get |r| times |a| from one call to the
first argument, so we need to call it |q| times.

|Maybe| and State instances of |Monad| thus become:\unsure{At (1) we
  have |r| times |x| and need to produce |1| time |x|. So we must have
  |r>=0| in the model.}
\begin{code}
data Maybe a where
  Nothing :: Maybe a
  Just :: a ⊸ Maybe a

instance Monad ω Maybe where
  return x = Just x -- (1)
  Just x >>= f = f x
\end{code}

\begin{code}
instance Monad 1 (Λr. Λs. s ⊸ (s⊗r a)) where
  return x s = (s,x)
  (ma >>= lmb) s = case ma s of
    (y,s) -> lmb y s
\end{code}

The above only points at several possible designs based on our system.
While experience will tell which option is the best, we have
demonstrated that several viable options exist.
\subsection{FFI}
\label{sec:ffi}

It is not uncommon for Haskell libraries to be shims over libraries
written in C. Sometimes, the underlying C library is also non
re-entrant. That is, they have a single global context, thus if ones
tries to call the C library several times from different logical
contexts, one will get incorrect results. A typical attempt to this
issue involves
\begin{itemize}
\item using a monadic interface to the library and,
\item having an existentially bound type parameter in the type:
  \begin{code}
    type M s a
    instance Monad (M s)

    primitive :: M s X
    runLowLevel :: M s a -> IO x
  \end{code}
\end{itemize}
The above solution is adequate as long as one refrains from calling
\begin{code}
forkIO :: IO a -> IO ()
\end{code}
Indeed, if one uses |forkIO|, there is a risk to call |runLowLevel|
several times concurrently.

Using linear types, one may instead provide an explicit and unique
instance of the context.
\begin{code}
type Context
initialContext :: _ 1 Context
\end{code}

The |Context| type will not have any runtime representation on the
\HaskeLL{} side.  It will only be used to ensure that primitive
operations can acquire a mutually exclusive access to the context.
\begin{code}
primitive :: Context ⊸ IO (Context ⊗ X)
\end{code}
One eventually wants to release the context (freeing whatever
resources that the C library has allocated), for example as follows:
\begin{code}
doneWithContext :: Context ⊸ IO ()
\end{code}
In practice, a top-level binding with weight $1$ will behave similarly
to |main|, in the sense that it may raise link-time type-errors.

\subsection{Primitive arrays}
\label{sec:primops}
One of the usage of linear types is to make memory management (semi-)
explicit. As an illustration we provide two possible APIs to
manipulate randomly addressable memory regions (so called ``byte
arrays'' in GHC parlance). We also propose a possible implementation
strategy for the primitives, and argue briefly for
correctness.\improvement{This makes sense because variables are linear
  and not affine (otherwise the arrays would need to be traversed by
  \textsc{gc}). This should be clarified.}
\improvement{example program (ideally measurements)}

\subsubsection{Version 1}
A possible API is the following:
\begin{code}
withNewByteArray :: Int → (MutableByteArray ⊸ Bang k) ⊸ k
updateByteArray :: Int -> Byte → MutableByteArray ⊸ MutableByteArray
freeByteArray :: MutableByteArray ⊸ ()
indexMutByteArray :: Int -> MutableByteArray ⊸ (MutableByteArray ⊗ Byte)
freezeByteArray :: MutableByteArray ⊸ Bang ByteArray
indexByteArray :: Int -> ByteArray -> Byte
\end{code}

\unsure{describe operational semantics for these things OR retire this
  and use arrays of 'something' \fref{sec:more-applications} }
\improvement{explain why freeze goes to the
  non-linear context, rather than just loosing capabilities.}

The key primitive in the above API is |withNewByteArray|, whose first
argument is the size of an array to allocate. The second argument is a
continuation where \emph{one} reference to the byte array is
available. Operationally, the function starts by allocating a byte
array of the requested size \emph{on a linear heap} and then calls the
continuation. It then forces the evaluation of the continuation in WHNF
(obtains the |Bang| constructor). The reference contained therein is
then returned. The type-system ensures that this reference does not
depend on any object in the linear heap.  This property is critical
when |withNewByteArray| is called $ω$ times.

To convince oneself of the correctness of the above semantics, one can
examine the following example:
\begin{code}
expensiveFunction :: ByteArray → Int

withNewByteArray n (\a ->
  case freezeByteArray a of
    Bang a' -> Bang (expensiveFunction a'))
\end{code}
In order to evaluate |Bang (expensiveFunction a')| to WHNF, one must
first evaluate |freezeByteArray a| to WHNF, and this operation turns
the linear reference into an unrestricted reference. In general, the
type-system ensures that the closure inside |Bang| contains no linear
variable, because the typing rules make it is impossible to transform
a $1$-weighted object into an $ω$-weighted one without copying it
explicitly.

Many functions from API take a |MutableByteArray| as argument and
produce a new |MutableByteArray|. Such functions can perform in-place
updates of the array (even though we remark that the
|MutableByteArray| is not a reference type) because linearity ensures
that it cannot be shared.

Finally, |freezeByteArray| turns a linear |MutableByteArray| into a
shareable |ByteArray|. It does so by moving the data from the linear
heap onto the \textsc{gc} heap. It consumes the static |MutableByteArray|,
so that no further function can access it. In particular, such a frozen
byte array can be returned by the argument to |withNewByteArray|:
\begin{code}
  withNewByteArray n freezeByteArray :: ByteArray
\end{code}

\todo{Add splitByteArray?}

\subsubsection{Version 2}

A possible shortcoming of the above API is that any code that performs
allocation must be written in continuation-passing style.  An
alternative API using direct style is the following:

\begin{code}
newByteArray :: Heap s ⊸ Int → (MutableByteArray s ⊗ Heap s)
updateByteArray :: Int -> Byte → MutableByteArray s ⊸ MutableByteArray s
freeByteArray :: MutableByteArray s ⊸ Heap s ⊸ Heap s
freezeByteArray :: MutableByteArray s ⊸ Heap s ⊸ (Heap s ⊗ Bang ByteArray)
withAHeap :: forall a. (forall s. Heap s ⊸ (Heap s ⊗ Bang a)) ⊸ a
\end{code}

The above API assumes a unique reference to a |Heap s|. The
|newByteArray| function takes a such a reference (and eventually
releases it), which ensures that it can never be called $ω$ times.

The |withAHeap| function creates such a unique reference. It uses the
same trick as |withNewByteArray| to ensure that linear objects do not
escape the intended scope.

Contrary to the first API, no |Bang| return type is necessary, because
the heap is threaded though all functions (take note that |freeze| and
|free| explicitly access the heap). Thus, by forcing the final state of
the heap in |withAHeap|, one ensures that no dangling reference to
linear array remains. Additionally, the |Bang a| type ensures that the
argument of |withAHeap| cannot return a reference to any mutable byte
array (or heap), as we have discussed for Version 1. 
\subsection{Fusion}
\label{sec:fusion}

A popular optimization for functional languages, and in particular
GHC, is \emph{shortcut fusion} \cite{gill_short_1993}.  Shortcut
fusion relies on custom rewrite rules and a general purpose
compile-time evaluation mechanism.

Concretely:
\begin{enumerate}
\item Rewrite rules transform structures which use general recursion
  into a representation with no recursion (typically church encodings)
\item The evaluator kicks in and fuses compositions of non-recursive
  functions
\item Unfused structures are reverted to the original representation.
\end{enumerate}

The problem with this scheme is that it involves two phases of
heuristics (custom rewrite rules and evaluator), and in practice
programmers have difficulties to predict the performance of any given
program subject to shortcut fusion. Additionally, it is not uncommon for a compiler
to even introduce sharing where the programmer doesn't expect it,
effectively creating a memory leak
(\url{https://ghc.haskell.org/trac/ghc/ticket/12620}).

A partial remedy to this situation is to stop relying on rewrite
rules, and use directly non-recursive representations. Doing so is
nowadays popular in libraries for efficient programming in Haskell
\cite{axelsson_feldspar_2010,lippmeier_parallel_2016,chakravarty_accelerating_2011,claessen_expressive_2012}.

For example, \textcite{lippmeier_parallel_2016} use the following
representation:

\begin{code}
-- |i| is the array's index type, |e| the type of elements and 'm' the
-- effects
data Sources i m e = Sources
  { arity :: i
   -- |pull| is an iterator to apply to every elements of the array
   -- (like |traverse|)
  , pull  :: i -> (e -> m ()) -> m () -> m () }

data Sinks i m e = Sinks
  { arity :: i
  , push  :: i -> e -> m ()
  , eject :: i -> m () }
\end{code}
Such representations are typically functionals, and thus do not
consume memory\footnote{proportionally to the input} and are never implemented using recursion. Thus, one
eventually gets code which is known to be fused. For instance, in the
following example from Lippmeier et al., neither the source nor the
sink represent data in memory:
\begin{code}
copySetP :: [FilePath] -> [FilePath] -> IO ()
copySetP srcs dsts = do
  ss <- sourceFs srcs
  sk <- sinkFs   dsts
  drainP ss sk
\end{code}

However, one then faces two classes of new problems.
%
First, any non-linear (precisely non-affine) use of such a
representation will \emph{duplicate work}. For example, one can write
the following piece of code, but the |expensiveComputation| will be
run twice, perhaps unbeknownst to the programmer.
%
\begin{code}
example srcs dsts = do
  ss <- expensiveComputation `ap` sourceFs srcs
  sk <- sinkFs  dsts
  drainP ss sk
  drainP ss sk
\end{code}

If one is not careful, one may end up with a program which does not
use any intermediate memory, but duplicates a lot of intermediate
computations. Linear types solve the problem by preventing such
duplications. (Combinators may be still provided to duplicate
computation explicitly or store intermediate results explicitly.)

Second, such representations may contain effects. In this situation,
non-linear uses may produce an \emph{incorrect program}. If one takes
the example of a non-recursive representation of files, one may have
two processes writing simultaneously in the same file (potentially
corrupting data), or one may forget to close the file.
Quoting \citeauthor{lippmeier_parallel_2016}:
\begin{quote}
  In general an object of type |Sources| is an abstract producer of
  data, and it may not even be possible to rewind it to a previous
  state --- suppose it was connected to a stream of sensor
  readings. Alas the Haskell type system does not check linearity so
  we rely on the programmer to enforce it manually.
\end{quote}
Linearity offers a direct solution to
\citeauthor{lippmeier_parallel_2016}'s worry about safety.  At the same
time, sharing becomes more explicit. In the above snippet, because
|srcs| have weight 1, so has |ss|, and thus it cannot be shared between the two instances of |drainP ss sk|.
The programmer has then the choice of either: 1. copying
the contents of |srcs| or 2. duplicating the computation; and the choice
must be written explicitly in the program.

Programming streaming libraries with explicit linearity has been
explored in detail by \textcite{bernardy_duality_2015}.

\paragraph{Semantics of the optimizer}

In order to perform inlining and fusion, GHC's optimizer performs
a cardinality analysis. Indeed, blindly inlining functions may worsen
the performance of a program. This is illustrated by the following
example found in \textcite{dominguez_parafusion_2006}:
\begin{code}
  tails :: [a] -> [[a]]
  tails (_ : xs) = xs : tails xs
  tails [] = []

  map :: (a -> b) -> [a] -> [b]
  map f (x : xs) = f x : map f xs
  map _ [] = []
\end{code}
We have that |force . tails . map (+1)| consumes memory linearly in
the size of its input whereas the fused
\begin{code}
  tailsmap :: (a -> b) -> [a] -> [[b]]
  tailsmap f (_ : xs) = map f xs : tailsmap f xs
  tailsmap _ [] = []
\end{code}
makes |force . tailsmap (+1)| consumes memory quadratically in the
size of its input.

This cardinality analysis is performed by the optimiser on a
best-effort basis. Instead, they must resort
to guesswork and and careful adherence to known-working patterns to
obtain efficient code.  In practice, the performance of any
non-trivial program is unpredicatble: any small change in the program
may significantly impact the performance of the compiled code.

Using linear types to make sure that the optimizer inlines a function
makes it possible to consider fusing optimisation part of the
semantics of the compiler, imposing that the optimizer honours the
intent of the programmer.

\section{\calc{} dynamics}
\label{sec:dynamics}

Supporting the examples of~\fref{sec:app} would require only surface changes to
an Haskell implementation: only the type system for \fref{sec:ffi} and
\fref{sec:primops}, while \fref{sec:fusion} only requires additional
annotations in the optimization phase.

If one is willing to dive deeper and modify the runtime system, a
further benefit can be reaped: prompt deallocation of thunks. While
this extension of the runtime system is necessary only to enjoy prompt deallocation of thunks,
the dynamic semantics presented in this section can also
help give confidence in the correctness of the extensions
of~\fref{sec:app}.

Concretely, we show that it is possible to allocate linear objects on
a heap which is not managed by the garbage collector, and
correspondingly deallocate them upon (lazy) evaluation. To do so we
present an extension of the semantics of
\textcite{launchbury_natural_1993} to \calc{}. Prompt
deallocation is not necessarily faster than garbage collection but it
reduces latencies and allows more control on when garbage-collection
pause occur.

\begin{figure}

  \figuresection{Syntax of the runtime language}
  \begin{align*}
    r &::=\\
      &||  x\\
      &||  λx. r\\
      &||  r x\\
      &||  λπ. r\\
      &||  r p\\
      &||  c x₁ … x_n\\
      &||  \case[q] r {c_k  x₁ … x_{n_k} → r_k}\\
      &||  \flet x_1 =_{q₁} r₁ … x_n =_{q_n} r_n \fin r
  \end{align*}

  \figuresection{Translation of typed terms}

  \begin{align*}
    (λ(x:_qA). t)^* &= λx. (t)^* \\
    x^*             &= x \\
    (t_q  x )^*     &= (t)^*  x \\
    (t_q  u )^*     &= \flet y =_{q} (u)^* \fin (t)^*  y \\
    c_k  t₁ … t_n   &= \flet x₁ =_{q_1} (t₁)^*,…, x_n =_{q_n} (t_n)^*
                      \fin c_k x₁ … x_n
  \end{align*}
  \begin{align*}
    (\case[p] t {c_k  x₁ … x_{n_k} → u_k})^* &= \case[p] {(t)^*} {c_k  x₁ … x_{n_k} → (u_k)^*} \\
    (\flet x_1:_{q₁}A_1= t₁  …  x_n :_{q_n}A_n = t_n \fin u)^* & = \flet x₁ =_{q₁} (t₁)^*,…, x_n=_{q_n} (t_n)^* \fin (u)^*
  \end{align*}

  \caption{Syntax for the Launchbury-style semantics}
  \label{fig:launchbury:syntax}
\end{figure}

A Launchbury-style semantics is a big-step semantics expressed in a
language suitable to represent sharing. The detail of this language
and the translation from \calc{} can be found in
\fref{fig:launchbury:syntax}. The main differences between \calc{} and
the runtime language are that the latter is untyped, has fewer weight
annotations, and applications always have variable arguments.

The complete semantics is given in \fref{fig:dynamics}.
Compared to \citeauthor{launchbury_natural_1993}'s original, our
semantics exhibits the following salient differences:
\begin{itemize}
\item The heap is annotated with weights. The variables with weight
  $ω$ represent the garbage-collected heap, while the variables with
  weight $1$ represent the non-garbage-collected heap, which we call
  the linear heap.
\item We add a weight parameter to the reduction relation,
  corresponding to the (dynamic) quantity of values to produce.
\item The rules for \emph{variable}, \emph{let}, and
  \emph{application} are changed to account for weights (let-bindings
  and application are annotated by a weight for this reason).
\end{itemize}

The dynamics assume that weight expressions are reduced
to a constant using weight-equality laws. If that is not possible the
reduction will block on the weight parameter.
The weight parameter of the reduction relation is used to interpret
$\flet x =_1 …$ bindings into allocations on the appropriate
heap. Indeed, it is not the case that $\flet x =_1 …$ bindings always
allocate into the linear heap: in $ω$ contexts, $\flet x =_1 …$ must
allocate on the \textsc{gc} heap, not on the linear one. To see why, consider
the following example:
%
\begin{code}
let f = _ ω (\y : _ 1 () -> case y of () -> let z = _ 1 True in z) in
let a = _ ρ f ()
\end{code}
%
The function $\varid{f} : () ⊸ Bool$ creates some boolean thunk, and this
thunk must be allocated in the linear heap if the context requires a
linear value, while if the context requires an unrestricted value, the
thunk must be allocated on the garbage-collected heap. However, the
thunk is allocated by $\flet z =_1 …$, so this let-binding may have to
allocate on the garbage-collected heap despite being annotated with
weight $1$. This behavior is not a consequence of implicit promotion
from $ω$ to $1$, but is intrinsic to using linear types. Indeed, even
pure linear logic features an explicit promotion, which also permits
linear functions to produce linear values which can be promoted to
produce unrestricted values.

In all evaluation rules, this dynamic weight is propagated to the
evaluation of subterms, sometimes multiplied by another weight
originating from the term. This means that, essentially, once one
starts evaluating unrestricted results (weight = $ω$), one will remain
in this dynamic evaluation mode, and thus all further allocations will
be on the \textsc{gc} heap. However, it is possible to provide a special-purpose
evaluation rule to escape dynamic evaluation to linear evaluation.
This rule concerns case analysis of |Bang x|:
\[
    \inferrule{Γ: t ⇓_{q} Δ : \varid{Bang} x \\ Δ : u[x/y] ⇓_ρ Θ : z}
    {Γ : \mathsf{case}_{q} t \mathsf{of} \{\varid{Bang} y ↦ u\} ⇓_ρ Θ : z}\text{case-bang}
\]
The observations justifying this rule is that 1. when forcing a |Bang|
constructor, one will obtain $ω$ times the contents. 2. the contents
of |Bang| (namely $x$) always reside on the \textsc{gc} heap, and transitively so. Indeed, because this
$x$ has weight $ω$, the type-system ensures that all the
intermediate linear values potentially allocated to produce $x$ must
have been completely eliminated before being able to return $x$.

The following function is a convenient wrapper around the case-bang
rule:
\begin{code}
withLinearHeap :: a ⊸ (a ⊸ Bang b) ⊸ b
withLinearHeap x k = case k x of
  Bang y -> y
\end{code}
Indeed, even when |withLinearHeap| is called $ω$ times, its argument
will be called $1$ time. In an implementation, one may prefer to
provide |withLinearHeap| as a primitive operation instead of having a
special-purpose implementation of |case|. In particular, when
implementing bindings to imperative APIs, any function of type |(A ⊸
Bang B) ⊸ C| may allocate |A| on a linear heap if it forces the
|Bang| constructor before returning the result (|C|).

\begin{figure}
  \begin{mathpar}
    \inferrule{ }{Γ : λπ. t ⇓_ρ Γ : λπ. t}\text{w.abs}


    \inferrule{Γ : e ⇓_ρ Δ : λπ.e' \\ Δ : e'[q/π] ⇓_{ρ} Θ : z} {Γ :
      e q ⇓_ρ Θ : z} \text{w.app}

    \inferrule{ }{Γ : λx. e ⇓_ρ Γ : λx. e}\text{abs}


    \inferrule{Γ : e ⇓_ρ Δ : λy.e' \\ Δ : e'[x/y] ⇓_{ρ} Θ : z} {Γ :
      e x ⇓_ρ Θ : z} \text{application}

    \inferrule{Γ : e ⇓_ω Δ : z}{(Γ,x ↦_ω e) : x ⇓_ρ (Δ;x ↦_ω z) :
      z}\text{shared variable}


    \inferrule{Γ : e ⇓_1 Δ : z} {(Γ,x ↦_1 e) : x ⇓_1 Δ :
      z}\text{linear variable}


    \inferrule{(Γ,x_1 ↦_{q_1ρ} e_1,…,x_n ↦_{q_nρ} e_n) : e ⇓_ρ Δ : z}
    {Γ : \flet x₁ =_{q₁} e₁ … x_n =_{q_n} e_n \fin e ⇓_ρ Δ :
      z}\text{let}

    \inferrule{ }{Γ : c  x₁ … x_n ⇓_ρ Γ : c  x₁ …
      x_n}\text{constructor}


    \inferrule{Γ: e ⇓_{qρ} Δ : c_k  x₁ … x_n \\ Δ : e_k[xᵢ/yᵢ] ⇓_ρ Θ : z}
    {Γ : \case[q] e {c_k  y₁ … y_n ↦ e_k } ⇓_ρ Θ : z}\text{case}

  \end{mathpar}

  \caption{Dynamic semantics}
  \label{fig:dynamics}
\end{figure}

The \emph{shared variable} rule also triggers when the weight
parameter is $1$, thus effectively allowing linear variables to look
on the garbage-collected heap, and in turn linear data to have unrestricted
sub-data.

\begin{lemma}[The \textsc{gc} heap does not point to the linear heap]
  It is an essential property that the garbage collected heap does not
  contain any reference to the linear heap. Otherwise, garbage collection
  would have to also free the linear heap, making the linear heap
  garbage-collected as well (the converse does not hold: there can be
  references to the garbage-collected heap from the linear heap,
  acting as roots).
\end{lemma}
\begin{proof}
To prove the above we need a typed version of the reduction
relation. (See \fref{fig:typed-semop}) The judgement $Γ:t ⇓_ρ Δ:z$ is extended to the form
$Ξ ⊢ (Γ||t ⇓ Δ||z) :_ρ A, Σ$, where
\begin{itemize}
\item $Ξ$ is a context of free variables
\item $Σ$ is a stack of typed terms which are yet to reduce
\item $t,z$ are typed terms
\item $Γ,Δ$ are heap states, that is associations of variables to
  typed and weighted terms.
\end{itemize}
We then show that this new relation preserves types. A well-typed
reduction state implies that the heap is consistent as per this lemma.
Hence, starting from a well-typed state, the reduction relation will
only produce consistent heaps.
\end{proof}

\begin{figure}
  \centering
\begin{definition}[Well-typed reduction relation]
  The judgement \[Ξ ⊢ (Γ||t ⇓ Δ||z) :_ρ A, Σ\] is defined inductively by
  the following rules:

\begin{mathpar}
\inferrule
  { }
  {Ξ ⊢ (Γ || λx.t  ⇓ Γ || λx.t) :_ρ A, Σ}
{\text{shared variable}}

\inferrule
    {Ξ  ⊢  (Γ||e      ⇓ Δ||λy.u):_ρ A →_q B, x:_{qρ} A, Σ \\
     Ξ  ⊢  (Δ||u[x/y] ⇓ Θ||z)   :_ρ       B,            Σ}
    {Ξ  ⊢  (Γ||e x ⇓ Θ||z) :_ρ B ,Σ}
{\text{app}}

\inferrule
  {Ξ, x:_ωB ⊢ (Γ||e ⇓ Δ||z) :_ρ A, Σ}
  {Ξ ⊢ (Γ,x :_ω B = e || x  ⇓ Δ, x :_ω B = z || z) :_ρ A, Σ}
{\text{shared variable}}

\inferrule
  {Ξ ⊢ (Γ||e ⇓ Δ||z) :_1 A, Σ}
  {Ξ ⊢ (Γ,x :_1 B = e|| x  ⇓  Δ||z) :_1 A,  Σ}
{\text{linear variable}}

\inferrule
  {Ξ ⊢ (Γ,       x_1 :_{ρq_1} A_1 = e_1 … x_n :_{q_n} A_n = e_n  ||  t ⇓ Δ||z) :_ρ C, Σ}
  {Ξ ⊢ (Γ||\flet x_1 :_{q_1}  A_1 = e_1 … x_n :_{q_n} A_n = e_n \fin t ⇓ Δ||z) :_ρ C, Σ}
{\text{let}}

\inferrule
  { }
  {Ξ ⊢ (Γ || c x_1…x_n  ⇓ Γ || c x_1…x_n) :_ρ A, Σ}
{\text{constructor}}

\inferrule
  {Ξ,y:_{pqρ} A ⊢ (Γ||e ⇓ Δ||c_k x_1…x_n) :_{qρ} D, u_k:_ρ C, Σ \\
   Ξ ⊢ (Δ||u_k[xᵢ/yᵢ] ⇓ Θ||z) :_ρ C, Σ}
  {Ξ ⊢ (Γ||\case[q] e {c_k y_1…y_n ↦ u_k} ⇓ Θ||z) :_ρ C, Σ}
{\text{case}}

\inferrule
   {Ξ,y:_ω A ⊢ (Γ||e ⇓ Δ||\varid{Bang}  x) :_1 D, u:_ω C, Σ \\
    Ξ ⊢ (Δ||u[x/y] ⇓ Θ||z) :_ω C, Σ}
   {Ξ ⊢ (Γ||\case[1] e {\varid{Bang}  y ↦ u} ⇓ Θ||z) :_ω C, Σ}
{\text{case-Bang}}
  \end{mathpar}
\end{definition}
  \caption{Typed operational semantics. (Omitting the obvious w.abs and w.app for concision)}
  \label{fig:typed-semop}
\end{figure}

\begin{definition}[Well-typed state]
  We write $Ξ ⊢ (Γ||t :_ρ A),Σ$ as a shorthand for
  \[
    Ξ ⊢ \flet Γ \fin (t,\mathnormal{terms}(Σ)) :
    (ρA⊗\mathnormal{weightedTypes}(Σ))‌
  \]
  In the above expression $\flet Γ$ stands in turn for a nested
  $\mathsf{let}$ expression where all variables in $Γ$ are bound to
  the corresponding term in $Γ$, with the given type and weight. We
  write $(ρA⊗\mathnormal{weightedTypes}(Σ))‌$ for the weighted tensor
  type comprised of $A$ with weight $ρ$, the types in $Σ$ and the
  corresponding weights.
\end{definition}

\begin{lemma}[The typed reduction relation preserves typing.]~\\
  if  $Ξ ⊢ (Γ||t ⇓ Δ||z) :_ρ A, Σ$, then
  \[Ξ ⊢ (Γ||t :ρ A),Σ \text{\quad{}implies\quad{}} Ξ ⊢ (Δ||z :ρ A),Σ.\]
\end{lemma}
\begin{proof}
  By induction.
\end{proof}


\subsection{Explicit memory management}
To illustrate how the semantics of \fref{fig:dynamics} works, let us
consider how it indeed allows explicit memory management of data in
the linear heap. Specifically, first-order inductive data types can
be cleared from the linear heap either by being freed, or by being
moved into the garbage-collected heap, without additional
primitives. To that effect, let us introduce the following \HaskeLL{}
type class:
\begin{code}
  class Data a where
    free  :: a ⊸ ()  -- Frees data in the linear heap
    move  :: a ⊸ Bang a  -- moves data from the linear heap to the \textsc{gc} heap
\end{code}
Now, let us demonstrate how to implement instance of |Data| for
booleans and lists, which should make it clear how to derive |Data| to
any data type:
\begin{code}
  data Bool = True | False

  instance Data Bool where
    free True   = ()
    free False  = ()

    move True   = Bang True
    move False  = Bang False

  data List a where
    []   :: List a
    (:)  :: a ⊸ List a ⊸ List a

  instance Data a => Data (List a) where
    free [] = ()
    free (x:l) = case free x of () -> free l

    move [] = Bang []
    move (x:l) =
    case (move x, move l) of
      (Bang x',Bang l') -> Bang (x':l')
\end{code}

The existence of |move| combined with lazy thunks may seem to
contradict the fact there are no references from the garbage collected
heap to the linear heap:
\begin{code}
  let  x  : _ 1 List Bool
          = [True,False]
       y  : _ ω Bang (List Bool)
          = move x
  in …
\end{code}
The thunk in |y| contains a pointer to |x| which lives in the linear
heap. Fortunately this is not the case: |move x| is a lazy thunk which
produces a \textsc{gc}-heap-allocated value, but the thunk itself is
not unrestricted and will go to the linear heap\footnote{To be
  entirely precise |move x| will go to the linear heap if the weight
  parameter is $1$, but if the weight parameter is $ω$ both $x$ and
  $ω$ will allocated to the garbage-collected heap.}. And, indeed, the
above snippet is ill-typed. Because we are trying to verify the
following judgement:
$$x:_1|List Bool|⊢ \flet y :_ω |move x| = …$$
while, per the \emph{let} typing rule, we would need:
$$x:_ω|List Bool|⊢ \flet y :_ω |move x| = …$$

In order to extract the unrestricted value from |move x| one has to
force the thunk with a case:
\begin{code}
  let x : _ 1 List Bool = [True,False]
  in case move x of Bang x' ->
  … -- |x'| is unrestricted
\end{code}

\subsection{Discussion: Affinity}

Consider the expression |let x = _ 1 e in let y = _ ω Just (x+1)
in …|. One remarks that, thanks to laziness, even if |y| has weight
$ω$, |x| will be demanded at most one time. Thus it is tantalizing
to allocate |x| on the linear heap.

But, because |x| is pointed to by |y| and |y| can be deallocated
without ever being used, the garbage collector may have to deallocate
|x| as well when |y| is deallocated. So, while it is possible to
promptly deallocate |x| when it is forced, |x| would still need to be
subject to garbage collection, hence garbage collection traversal,
which runs afoul of the goal of diminishing the pressure on the
garbage collector.

Variables which will be used at most once are called
\emph{affine}. Linear variables, by contrast, \emph{must} be used
\emph{exactly} once. The fact that linear variables must be used allow
more optimizations to be applied than to affine variables.

\section{Applications of dynamic semantics}
\label{sec:more-applications}
\subsection{Linear Arrays}
Given the above operational semantics of \fref{sec:dynamics}, one can
propose an API for non-\textsc{gc} arrays and semantics for them.
The proposed API is the following:

\begin{code}
withNewArray :: Int -> a -> (Array a ⊸ Bang k) ⊸ k
updateArray :: Int → a ⊸ Array a ⊸ (Array a ⊗ a)
splitArray :: Int → Array a ⊸ (Array a ⊗ Array a)
foldArray :: b ⊸ (Int → a ⊸ b ⊸ b) → Array a ⊸ b
arraySize :: Array a ⊸ (Int ⊗ Array a)
\end{code}

\paragraph{Denotational semantics}
We can give a semantics simply by representing the type |Array| and
the API functions in terms of \HaskeLL. This denotational semantics
does not preclude a more efficient implementation.\improvement{Even if
  we don't implement prompt-deallocation of cons cells we can have
  arrays out of the \textsc{gc} heap, such as these. But we would need to
  restrict the class of type |a| and |b| in most the API functions
  (probably to |Storable|)}

The interpretation of the array type is simply that of a linear list, as
defined above:
\begin{code}
type Array = List
\end{code}

The allocation of a new array needs to guarantee that local usage of
the array are linear and can operate in the linear heap. To do so we
leverage the case-bang rule described in the previous section.
\begin{code}
replicate :: Int -> a -> List a
replicate 0 x = []
replicate n x = x:replicate (n-1) x

withNewArray n x k = case k (replicate n xs) of
  Bang r -> r
\end{code}

The rest of the API is interpreted by recursive functions over lists.
We stress that thanks to linearity the new lists will not go to the \textsc{gc}.
The implementation is as follows:
\begin{code}
updateArray 0 y (x:xs)   = (x, y:xs)
updateArray n y []       = (error "array too small!") y
updateArray n y (x:xs)   = case updateArray (n-1) y xs of
  (y',xs') -> (y',x:xs')

splitArray n []      = []
splitArray 0 xs      = ([],xs)
splitArray n (x:xs)  = case splitArray (n-1) xs of
  (ys,zs) -> (x:ys,zs)

foldArray k _    []        = k
foldArray k (+)  (x:xs)    = x + foldArray k xs

arraySize []      = (0,[])
arraySize (x:xs)  = case byteArraySize xs of
  (n,ys) -> (1+n,y:ys)
\end{code}

\paragraph{Operational semantics}
Of course, an efficient implementation should not represent arrays as
lists, requiring $O(n)$ traversals. Thus it may be useful to spell out
a possible operational semantics which represents arrays natively. The
semantics of |withNewArray| and |updateArray| is as follows:
\begin{mathpar}
  \inferrule{Γ_1:n ⇓_ω Γ₂:n'\\
    Γ₂:k ⇓_ρ Γ_3:λy.t[y]\\
    Γ_3,y↦_1[x…x]:t ⇓_1 Γ_4:\Conid{Bang} z
  }
  {Γ₁:\Varid{withNewArray} n x k ⇓_ρ Γ_4:z}

  \inferrule{Γ:n ⇓_ω Δ:n'
  }
  {Γ,y↦_1[x_1…x_m] :\Varid{updateArray} n x y ⇓_1 Δ,y↦_1[x_1…x_{n'-1},x,x_{n'+1}…x_m]:(y,x_{n'})}
\end{mathpar}
As for the case-bang rule, we can run the continuation of
|withNewArray| with weight 1 because we eventually extract the result
from a |Bang|. Consequently the |updateArray| rule needs only to
handle the 1 weight. Indeed the type-system will ensure that |Array|s
will ever have static weights of 1, and because we start with a
dynamic weight of 1 we can never end-up with weight $ω$ for an array.

We omit the semantics of other combinators, which are similar to the
|updateArray| rule.


\subsection{Prompt deallocation of cons cells}

Up until this point, we have only demonstrated how to achieve memory
safety and prompt deallocation by combining both linear types and
foreign heaps. Ideally, users shouldn't have to buy-in to foreign
heaps with explicit allocation and explicit object copies to and from
each heap just to get prompt deallocation. So to go even further, the
runtime system can be modified to allow regular Haskell data (which we
will refer as \emph{cons cells}), as opposed to just primitive data,
to reside out of the GC heap as long as it has been allocated
by a linear binding.

With such a modification, we can arrange for the messages that are
evicted from the queue API in \fref{sec:ffi} to also reside
outside of the GC heap. In this way, using the queue could
entail zero GC allocation. Predictable latencies would be
within reach.

To illustrate how it works, consider the following implementation of
the Fibonacci function based on matrix multiplication:
\begin{code}
fib :: Int ⊸ Int
fib n =
  case (free x21,x22) of
    ((),()) -> x11+x12
  where
    (Matrix x11 x12 x21 x22) :: _ 1 Matrix = expMatrix (n-1) (Matrix 0 1 1 1)

-- Like every data type, |Int| can be duplicated or dropped linearly
dup :: Int ⊸ (Int,Int)
free :: Int ⊸ ()

data Matrix where
  Matrix :: Int ⊸ Int ⊸ Int ⊸ Int ⊸ Matrix

-- With a bit of care, matrix multiplication can be implemented
-- linearly. This assumes a linear implementation of |(+)| and |(*)|
-- for integers.
multMatrix : Matrix ⊸ Matrix ⊸ Matrix
mult (Matrix x11 x12 x21 x22) (Matrix y11 y12 y21 y22) =
    Matrix
     (x11'*y11'+x12'*y21')
     (x11''*y12'+x12''*y22')
     (x21'*y11''+x22'*y21'')
     (x21''*y12''+x22''*y22'')
  where
    (x11',x11'') :: _ 1 (Int,Int) = dup x11
    (x12',x12'') :: _ 1 (Int,Int) = dup x12
    …

dupMatrix :: Matrix ⊸ (Matrix,Matrix)
dupMatrix = …

-- This function uses patterns which Haskell does not naturally
-- understands as a short hand for a view data type.
expMatrix :: Int ⊸ Matrix ⊸ Matrix
expMatrix 0        _m  = Matrix (1 0 0 1)
expMatrix (2*n)    m   = square m
expMatrix (2*n+1)  m   =
  let (m',m'') :: _ 1 (Matrix,Matrix) = dupMatrix m
  mult (square m') m''
where
  square m =
    let (m',m'') :: _ 1 (Matrix,Matrix) = dupMatrix m
    in multMatrix m' m''
\end{code}
\improvement{Jean-Philippe remarks that, in practice, a better type
  for the |Matrix| constructor is |Int#->Int#->Int#->Int#->Matrix|,
  that is arguments are unboxed and $ω$-weighted (the idea is that
  unboxed typed are not allocated on the heap so they can be
  $ω$-weighted for free). Arnaud designed this example with the
  objective of illustrating how linear types worked, and wanted to
  avoid making such distinction, but this is open for a debate.}

Because all the allocation of matrices happen in linear let-bindings,
it is possible to allocate all of them out of the GC heap,
\emph{as long as the result is used linearly}. To understand where
this limitation comes from, consider the following example:
\begin{code}
  forget :: Int -> ()
  forget _i = ()

  forget (fib 42)
\end{code}
Here |fib 42| is promoted to weight $ω$ because |42|, being a literal,
has weight $ω$. But then |fib 42| is dropped without being forced so
it needs to be garbage collected, as well as every value in the
closure. A partial evaluation of |fib 42| may cause the intermediate
matrices to be pointed to by the closure. Therefore, they need to be
garbage collected and cannot be allocated out of the GC heap.
A similar issue occurs when the return value of |fib 42| is used
several times.

To ensure that the linearly-bound matrices are allocated on the
GC heap, one must ensure that the result of |fib| is copied
to the GC heap at the end of the computation. This is done in
two parts. First the result is wrapped in a |Bang| using the |copy|
function (|Int|, like every data type, implements this method):
\begin{code}
  copy :: Int ⊸ Bang Int
\end{code}
Then, the |Bang| constructor is forced using a pattern-matching. This
has the effect of producing an |Int| closure of weight $ω$, hence on
the GC heap. The run-time system is allowed to assume that no
linear value are still live at this point (a $ω$-weighted value is
statically guaranteed to have no reference to linear bindings)
therefore that they can all be allocated, and managed, out of the
GC heap.

Revisiting our |forget| example, we can write:
\begin{code}
  case copy (fib 42) of
    Bang x -> forget x
\end{code}
In this expression, all the intermediate matrices can safely be
allocated out of the GC heap and be deallocated by
the run-time system at the point where they are consumed. The downside
being that we will run |fib 42| to completion even if the result is
not actually needed.


\begin{aside}\paragraph{Alternative: scratch regions}
An alternative to allocating linear cons cells using a malloc-like
discipline and freeing them immediately at case matching is to
allocate cons-cells in temporary scratch regions which are to be
discarded at the end of a computation. To be able to allocate data in
regions outside of the \textsc{gc} heap also requires a modification
of the run-time system, albeit probably a lighter one.

Linear types provide ways to design an \textsc{api} for such scratch
region. Let us give an example such design: the idea is to (locally)
allocate linear bindings to a scratch region while non-linear bindings
are allocated to the \textsc{gc} heap. This way, when all the linear
bindings have been consumed, it is safe to free the region.

The proposed \textsc{api} revolves around two functions: |withRegion|,
which allocates a scratch region to perform a computation and frees
the region at the end of that computation, and |inRegion| which runs a
computation such that the linear bindings are allocated on a given
region. Here is an \textsc{api} specifying this idea:
\begin{code}
  -- Creates a new region, linearity of the binding ensures that the
  -- region, and everything within, must be consumed. The region is
  -- freed at the end of the computation.
  withRegion :: (Region ⊸ Bang a) ⊸ a
  -- forks the region into two handles, each handle, still being of
  -- linear weight must be consumed before the |withRegion|
  -- computation is ended
  dupRegion :: Region ⊸ Region ⊗ Region
  -- computes |a| allocating linear binding in the region
  inRegion :: Region ⊸ a ⊸ a
  -- All pending regions must be dropped before the computation
  -- ends. |drop| only makes the binding inaccessible, the region is
  -- actually freed at the end of |withRegion|
  drop :: Region ⊸ ()
\end{code}
Like with previous examples, |withRegion c| is safe because the return
type of |c| is |Bang a| which means that it cannot contain reference
to linear bindings, \emph{i.e.} neither a region nor data allocated in
a region can escape |withRegion c|. A region allocated by |withRegion|
cannot be freed before the end of the |withRegion| computation because
even if all the region handles are inaccessible, there may still be
values allocated in regions which are accessible and are yet to be
dropped or copied to the \textsc{gc} heap. Therefore regions obey a
stack discipline. Linearly weighted data can transparently refer to
data allocated in any number of existing regions, since calls to
|inRegion| can be safely nested or interleaved.
\end{aside}

\section{Alternative designs}

\subsection{An ILL-guided design}
\label{sec:ill}

Simply using linear logic --- or, as it were, intuitionistic linear
logic, because we do not require a notion of type duality --- as a type
system would not suffice to meet our goal that a (intuitionistic,
lazy) $\lambda$-calculus be a subset of \calc{}. Indeed, even if
intuitionistic $\lambda$-calculus can be embedded in linear
$\lambda$-calculus, this embedding requires an encoding. Usually, one
would have a linear arrow $A⊸B$ and the usual unrestricted (intuitionistic) arrow would be
encoded as ${!}A ⊸ B$, where a value of type ${!}A$ represents an
arbitrary quantity of values of type $A$.

This encoding means that the quantity of available values must be managed
manually, and the common case (\emph{i.e.} an arbitrary quantity is required)
requires additional syntax. For instance, in \HaskeLL{}, we could not write the
following:
\begin{code}
  dup :: a -> a⊗a
  dup x = (x,x)
\end{code}
and we would be forced to write:
\begin{code}
  dup :: Bang a ⊸ a⊗a
  dup (Bang x) = (x,x)
\end{code}
When composing functions we would also have to manage the quantity of
the output of the intermediate functions:
\begin{code}
  id :: Bang a ⊸ a
  id (Bang x) = x

  v = dup (Bang (id (Bang 42)))
\end{code}

In sum, all the existing code which uses the same value several times
has to be re-written. This rewriting is mechanical, but deep: in
technical terms, it amounts to using the co-Kleisli category of |Bang|
(which is incidentally a co-monad).

\subsection{Linearity as a property of types vs. a property of bindings}

In several presentations \cite{wadler_linear_1990,mazurak_lightweight_2010,morris_best_2016}
programming languages incorporate
linearity by dividing types into two kinds. A type is either linear
or unrestricted. Unrestricted types typically includes primitive types
(such as \varid{Int}), and all (strictly positive) data types. Linear types
typically include resources, effects, etc.

A characteristic of this presentation is that linearity ``infects''
every type containing a linear type. Consequently, if we want to make
a pair of (say) an integer and an effect, the resulting type must be
linear. This property means that polymorphic data structures can no
longer be used \emph{as is} to store linear values. Technically, one
cannot unify a type variable of unrestricted kind to a linear
type. One can escape the issue by having polymorphism over kinds;
unfortunately to get principal types one must then have subtyping between
kinds and bounded polymorphism.

In contrast, in \calc{} we have automatic scaling of linear types to unrestricted
ones in unrestricted contexts. This feature already partially
addresses the problem of explosion of types. In order to give suitably general
types we need quantification over weights, and extension of the
language of weights to products and sums.

Another issue with the ``linearity in types'' presentation is that it
is awkward at addressing the problem of ``simplified memory
management'' that we aim to tackle. As we have seen, the ability to
use an intermediate linear heap rests on the ability to turn a linear
value into an unrestricted one. When linearity is captured in types,
we must have two versions of every type that we intend to move between
the heaps. Even though \textcite{morris_best_2016} manages to largely
address the issue by means of polymorphism and constraints over types,
it comes as the cost of a type-system vastly more complex than the one
we present here.


\subsection{Session types vs. linear types}

\Textcite{wadler_propositions_2012} provides a good explanation of the
relation between session types vs. linear types (even though the paper
contains some subtle traps --- notably the intuitive explanation of
par and tensor in LL does not match the semantics given in the
paper.). In sum, session types classify `live' sessions with
long-lived channels, whose type ``evolves'' over time. In contrast,
linear types are well suited to giving types to a given bit of
information. One can see thus that linear types are better suited for
a language based on a lambda calculus, while session types are better
suited for languages based on a pi-calculus and/or languages with
effects. Or put another way, it is a matter of use cases: session
types are particularly aimed at describing communication protocols,
while linear types are well suited for describing data. One is
communication centric, the other is data centric, yet there is a
simple encoding from session types to linear types (as Wadler
demonstrates in detail). In practice, we find that plain linear types
are perfectly sufficient to represent protocols, as as we show in
\fref{sec:protocols}.

\subsection{Related type systems}

\Textcite{mcbride_rig_2016} presents a similar type-theory, but with
weighted type judgement $Γ ⊢_ρ t : A$. In the application rule, the
weight is multiplied by the weight of the function in the argument. At
the point of variable usage one checks that the appropriate quantity
of the variable is available. A problem with this approach\todo{Thanks Ryan}{} is that
whenever one enters an $ω$-weighted judgement, one effectively
abandons tracking any linearity whatsoever. Thus, the following
program would be type-correct, while |dup| is duplicating a linear
value.

\[
(λ (dup : _ ω a ⊸ (a ⊗ a) ) . dup) (λx. (x,x))
\]

Effectively, in \citeauthor{mcbride_rig_2016}'s system, one cannot use
abstractions while retaining the linearity property. In that respect,
our system is closer to that of \textcite{ghica_bounded_2014}, which
does not exhibit the issue. The differences between our type system
and that of \textcite{ghica_bounded_2014} is that 1. we work with a
concrete set of weights 2. we support a special case-analysis
construction which works only for non-zero weights.

\section{Other related work}
\subsection{Operational aspects of linear languages}

Recent literature is surprising silent on the operational aspect of
linear types, and concentrates rather on uniqueness types
\cite{pottier_programming_2013,matsakis_rust_2014}.

Looking further back, \textcite{wakeling_linearity_1991} produced a
complete implementation of a language with linear types, with the goal
of improving the performance. Their implementation features a separate
linear heap (as we do in \fref{sec:dynamics}). They did not manage to
obtain consistent performance gains. However, they still manage to
reduce \textsc{gc} usage, which may be critical in distributed and
real-time environments, as we explained in the introduction.
Thus the trade-off is beneficial is certain situations.

Regarding absolute performance increase,
\citeauthor{wakeling_linearity_1991} propose not attempt prompt free
of thunks, and instead take advantage of linear arrays. \todo{Run concrete examples and see what we get.}

% \item Linear Lisp. \cite{baker_lively_1992}: unclear results

% \item LineralML \url{https://github.com/pikatchu/LinearML/}: no pub?


\section{Extensions and Future Work}

\unsure{Weight inference? Polymorphism? Magic |copy| of data structures?}

\subsection{More Weights}

To keep things concrete, we have limited the constants of the language
of weights to $1$ and $ω$. Yet, we could have more constants.  For
example, we could add $α$ to represent affine variables (usable zero
or once). In this situation we would have $α + 1 = ω$, $α · ω = ω$,
and the variable rule should be extended to $α$-contexts. Similarly one
can add a $0$, as \textcite{mcbride_rig_2016} does, and in turn
support dependent types.

We can even make the set weight constants be $2^ℕ$, with the obvious
operations, and the variable rule adapted accordingly.

\subsection{TODOs}
\begin{itemize}
\item What kind of top-level application are we mostly interested in?
  Long-lived? Allocation pattern?
\end{itemize}

\section{RTS Implementation strategy}

In terms of implementation, the dynamic semantics unfolds as:

\begin{itemize}
\item When doing case analysis of a linearly-typed input, one should
  check if the object comes from the linear heap. If it does, then the
  case analysis should behave specially. (Probably deallocate the
  object on the spot.). Note in particular that regular objects can be
  passed to functions expecting a linear object. So one MUST check
  where the data comes from before performing eager deallocation.
\item When making an allocation, one should check the ``dynamic ρ
  flag''. If $ρ=1$, then the allocation should happen on the linear
  heap. We say ``should'' because, as we have seen above, linear
  objects can always be allocated on the GC heap. One can summarize
  this fact as: $ρ=ω$ is a safe approximation of $ρ=1$.
\end{itemize}

We can implement the ``dynamic ρ flag'' as specialisation: each
function will have two implementations, one with $ρ=1$ and one with
$ρ=ω$. Because $ρ=ω$ is a safe approximation of $ρ=1$, we do not
\emph{have to} specialize any given function. Doing so is only going
to have an impact on performance, not on correctness.

\section{Conclusion}

The calculus \calc{} demonstrates how an existing lazy language, such
as Haskell, can be extended with linear types, without compromising
the language, in the following sense:
\begin{itemize}
\item Existing programs are valid in the extended language
  \emph{without modification}.
\item Such programs retain the same semantics.
\item Furthermore, the performance of existing programs is not affected.
\end{itemize}
In other words: regular Haskell comes first. Additionally, linearly
typed functions and data structures are usable directly from regular
Haskell code. In such a situation their semantics is that of the same
code with linearity erased.  When the programmer is ready to pay the
cost of finely dealing with usage through linearity, they get the
additional benefits of linear type: new abstractions
(\fref{sec:protocols}, \fref{sec:resources}, and \fref{sec:ffi}),
lower \textsc{gc} pressure (\fref{sec:primops}), control over
occurrence of \textsc{gc} pauses (\fref{sec:fusion} and
\fref{sec:dynamics}). All these benefits induce no penalty to
unmodified Haskell.

The benefits can be classified in three stages depending on how much
modification to an existing language they require:
\begin{enumerate}
\item Adapting the \textbf{type system} enables
  \begin{itemize}
  \item new abstractions such as protocols (\fref{sec:protocols}) and
    safe resource management (\fref{sec:resources})
  \item pure abstractions to C libraries (\fref{sec:ffi})
  \item primitive operations to keep data out of the garbage collector
    (\fref{sec:primops})
  \end{itemize}
\item Propagating type annotation to the \textbf{intermediate
    language} makes it possible to exploit linear types for further
  optimization (\fref{sec:fusion})
\item Modifying the \textbf{run-time system} further enables prompt
  deallocation of thunks which can be leveraged to prevent \textsc{gc} pauses
  in critical computations (\fref{sec:dynamics}).
\end{enumerate}

Of these three stages, modifying the type system is the cheapest, but
also the most immediately beneficial, enabling a lot of new uses for the
programming language. Propagating the information down to the run-time
system is still worth pursuing as we are expecting significant
benefits, due to reduced and controlled latency, for systems
programming, and in particular for distributed applications.

\printbibliography
\end{document}





%  LocalWords:  FHPC Lippmeier al honda pq th FFI monadic runLowLevel
%  LocalWords:  forkIO initialContext runtime doneWithContext Primops
%  LocalWords:  deallocation Launchbury launchbury GC scrutinee dup
%  LocalWords:  centric polymorphism modality intuitionistic typable
%  LocalWords:  compositional Andreoli's openfile myfile ReadMore ys
%  LocalWords:  hClose xs GC'ed deallocated linearities mcbride snd
%  LocalWords:  unboxed Haskellian APIs newByteArray MutableByteArray
%  LocalWords:  updateByteArray freeByteArray indexMutByteArray et ss
%  LocalWords:  freezeByteArray ByteArray indexByteArray Unfused srcs
%  LocalWords:  evaluator lippmeier functionals copySetP FilePath sk
%  LocalWords:  dsts sourceFs sinkFs drainP expensiveComputation WHNF
%  LocalWords:  duplications bernardy deallocate morris latencies gc
%  LocalWords:  doSomethingWithLinearHeap untyped boolean withFile ap
%  LocalWords:  forall aspiwack dually involutive runComputation lmb
%  LocalWords:  withNewByteArray expensiveFunction affine booleans zs
%  LocalWords:  Kleisli ghica wakeling TODOs Haskell subtype IOClient
%  LocalWords:  OpenFile IOServer shareable openFile monads withAHeap
%  LocalWords:  splitByteArray withLinearHeap weightedTypes foldArray
%  LocalWords:  optimizations denotational withNewArray updateArray
%  LocalWords:  splitArray arraySize Storable byteArraySize natively
