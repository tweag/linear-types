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
\bibliography{PaperTools/bibtex/jp.bib,local.bib}
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

\author{JP Bernardy, Mathieu Boespflug, Arnaud Spiwack}
\date{CONSIDER READING HaskeLL.lhs INSTEAD \today}
\title{Intuiting linear types}
\hypersetup{pdflang={English}}

\begin{document}

\maketitle
\begin{abstract}
``The case for resource aware type systems'' argued for teaching
  a notion of resource to GHC's type system. We show how adding
  a notion of linear types, a particular form of resource typing,
  addresses the challenges exposed therein.
\end{abstract}

\section{Linear types for resource management}

We argue that linear types offer a solution to static resource
management and help address the challenges of latency. The benefits
from linear types can be gained incrementally:

\begin{enumerate}
\item First, to provide a {\em safe} API to resources exposed as
  foreign resources allocated in a foreign heap.
\item Then, linearity can be exploited in the optimizer for safe and
  systematic fusion.
\item Finally, modifications to the runtime system make it possible to
  have type-directed allocation of objects. An API for explicit
  allocation and freeing of resources is no longer needed.
\end{enumerate}

Each of these stages imply increasingly invasive changes to the
compiler, but also increasingly large benefits. In practice it makes
it possible to roll out stages one at a time, quickly reaping the low
hanging fruits.

The philosophy behind the design of the linear type extension is that
it strictly extends Haskell as it existed before linear types: {\em
  every Haskell program is still a well-typed program in the
  linear-type extension and runs with no performance penalty}. This is
in contrast with languages such as Rust, which are specifically
optimized for writing programs that are structured using the RAII
pattern\footnote{\url{https://en.wikipedia.org/wiki/Resource_acquisition_is_initialization}}
(where resource lifetimes are tied directly or indirectly to stack
allocated objects that are freed when the control flow exits the
current lexical scope). Ordinary functional programs seldom fit this
particular resource acquisition pattern so end up being second class
citizens.

\subsection{Binding foreign functions}
\label{sec:ffi}

In a companion document\todo{name the document}, Bernardy and Spiwack propose a programming
language featuring two arrow types: one for the usual unrestricted
function space and one for linear functions. The latter are
extensionally equivalent to regular functions but are guaranteed to
consume their argument \emph{exactly once}. To be precise, the arrow
type is parametrized by the amount (hereafter referred to as the
\emph{weight}) of its argument that it requires:
\begin{itemize}
\item $A →_1 B$ is the linear arrow $A ⊸ B$,
\item $A →_ω B$ is the usual intuitionistic arrow $A → B$.
\end{itemize}
For instance the following data declaration
\begin{code}
data List a where
  [] :: List a
  (:) :: a ⊸ List a ⊸ List a
\end{code}
defines a linear version of the list type. That is, given a list with
weight $1$, every branch of any function that consumes the list must
refer to each item in the list exactly once.

Many list-based functions conserve the quantity of data, and thus can
be given a linear type. For example we can write |(++)| as follows:
\begin{code}
(++) :: List a ⊸ List a ⊸ List a
[]      ++ ys = ys
(x:xs)  ++ ys = x : (xs ++ ys)
\end{code}
What does this tell us? It means that if we have quantity $1$ of
a list |xs|, appending any other list to it will never duplicate any
of the elements in |xs|, nor drop any element in |xs|. Note that in
our system, giving a more precise type to |(++)| strengthens the
contract that the implementation of |(++)| must satisfy, but it
doesn't restrict its usage. It's perfectly legal to provide an $ω$
quantity |xs| as an argument, or indeed to {\em promote} the result of
the function, of quantity $1$, to quantity $ω$. The intuition is, in
a context that wants zero or more of a resource, providing exactly one
of that resource will do\improvement{clarify promotion: no dependency
  on resource or something to that effect}.

Of course, not all programs are linear: a function may require $ω$
times its input, even to construct a single output. For example the
function repeating its input indefinitely cannot be ascribed a type
with a linear arrow, because |l| appears twice in the RHS:
\begin{code}
cycle :: List a → List a
cycle l = l ++ cycle l
\end{code}

One might be tempted to mark all constructor types as linear, \emph{i.e.}
with only |⊸|-arrows in their types, in the style of the |List| type
above. After all, linear constructors, like any linear function, are
happy to be provided resources\improvement{resource is probably not
  the right word here} of any weight. However, $ω$-weighted
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

\todo{Probably add a remark that functional in-place update is not a goal}

\subsection{Guiding fusion}

A popular optimization for functional languages, and in particular
GHC, is \emph{shortcut fusion} \cite{gill_short_1993}.  Shortcut
fusion relies on custom rewrite rules and a general purpose
compile-time simplifier mechanism.

Concretely:
\begin{enumerate}
\item Rewrite rules transform structures which use general recursion
  into a representation with no recursion (typically church encodings)
\item The simplifier kicks in and fuses compositions of non-recursive
  functions
\item Unfused structures are reverted to the original representation.
\end{enumerate}

The problem with this scheme is that it involves two phases of
heuristics (custom rewrite rules and evaluator), and in practice
programmers have difficulties to predict the performance of any given
program subject to shortcut fusion. Additionally, it is not uncommon
for a compiler to even introduce sharing where the programmer doesn't
expect it, effectively creating a memory leak
(\url{https://ghc.haskell.org/trac/ghc/ticket/12620}).

A partial remedy to this situation is to stop relying on rewrite
rules, and use directly non-recursive representations. Nowadays, doing
so is popular in libraries for efficient programming in Haskell
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
consume memory\footnote{proportionally to the input} and are never
implemented using recursion. Thus, one eventually gets code which is
known to be fused. For instance, in the following example from
Lippmeier et al., neither the source nor the sink represent data in
memory:
\begin{code}
copySetP :: [FilePath] -> [FilePath] -> IO ()
copySetP srcs dsts = do
  ss <- sourceFs srcs
  sk <- sinkFs   dsts
  drainP ss sk
\end{code}

However, one then faces two classes of new problems.
%
First, any non-linear (or to be precise, non-affine) use of such
a representation will \emph{duplicate work}. For example, one can
write the following piece of code, but the |expensiveComputation| will
be run twice, perhaps unbeknownst to the programmer.
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
duplications. (Combinators may still be provided to duplicate
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
\citeauthor{lippmeier_parallel_2016}'s worry about safety. At the same
time, sharing becomes more explicit. In the above snippet, because
|srcs| have weight 1, so has |ss|, and thus it cannot be shared
between the two instances of |drainP ss sk|. The programmer has then
the choice of either: 1. copying the contents of |srcs| or 2.
duplicating the computation. The choice must be written explicitly in
the program.

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

\paragraph{Alternative: scratch regions}

An alternative to allocating linear cons cells using a malloc-like
discipline and freeing them immediately at case matching is to
allocate cons-cells in temporary scratch regions which are to be
discarded at the end of a computation. To be able to allocate data in
regions outside of the GC heap also requires a modification
of the run-time system, albeit probably a lighter one.

Linear types provide ways to design an API for such scratch
regions. Let us give an example such design: the idea is to (locally)
allocate linear bindings to a scratch region while non-linear bindings
are allocated to the GC heap. This way, when all the linear
bindings have been consumed, it is safe to free the region.

The proposed API revolves around two functions: |withRegion|,
which allocates a scratch region to perform a computation and frees
the region at the end of that computation, and |inRegion| which runs a
computation such that the linear bindings are allocated on a given
region. Here is an API specifying this idea:
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

\printbibliography

\end{document}
