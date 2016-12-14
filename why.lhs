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

\section{Linear types for resource management}

We argue that linear types offer a solution to static resource
management and help address the challenges of latency. The benefits
from linear types are splits into three stages:

\begin{enumerate}
\item Use a linear type system to create \textsc{ffi} bindings
\item Use linearity in the optimiser for fusion
\item Modify the run-time system to make zero-allocation possible
\end{enumerate}

Each of these stages requires additional change to the compiler to
implement, and brings further benefits. In practice it makes it
possible to roll stages one at a time, quickly reaping the low hanging
fruits.

The philosophy behind the design of the linear type extension is that
it strictly extends Haskell as it exists before linear types: every
Haskell program is still a well-typed program in the linear-type
extension and runs with no performance penalty. This is in contrast
with languages such as Rust which are optimised for linearly typed
programs but where ordinary functional programs are second class
citizens.

\subsection{Binding foreign functions}
\label{sec:ffi}

We propose a programming language with two arrow types: one for usual
intuitionistic functions, and one for linear functions~---~which
guarantee to consume their argument \emph{exactly once}. To be precise, the
arrow type is parametrized by the amount (hereafter referred to as the
\emph{weight}) of its argument that it requires:
\begin{itemize}
\item $A →_1 B$ is the linear arrow $A ⊸ B$
\item $A →_ω B$ is the usual intuitionistic arrow $A → B$
\end{itemize}
For instance the following data declaration
\begin{code}
data List a where
  [] :: List a
  (:) :: a ⊸ List a ⊸ List a
\end{code}
defines a linear version of the list type. That is, given a list with
weight $1$, one will obtain \emph{exactly one} instance of each of the
items contained inside it. Thus the above list may contain resources
without compromising safety.

Many list-based functions conserve the quantity of data, and thus can
be given a linear type. For example we can write |(++)| as follows:
\begin{code}
(++) :: List a ⊸ List a ⊸ List a
[]      ++ ys = ys
(x:xs)  ++ ys = x : (xs ++ ys)
\end{code}

Yet, conceptually, if one has a quantity $ω$ of both inputs, one can
call |(++)| $ω$ times to obtain a quantity $ω$ of the concatenation.
This reasoning hold on weights: if both arguments of |(++)| have
weight $ω$, the result of |(++)| can be \emph{promoted} to have weight
$ω$. Therefore giving a linear type to |(++)| is \emph{more precise}
than the regular type and does not lose generality.

Of course, not all programs are linear: a function may require $ω$
times its input, even to construct a single output. For example the
function repeating indefinitely its input will have the type:
\begin{code}
cycle :: List a → List a
cycle l = l ++ cycle l
\end{code}
\todo{Remark that |(++)| and |cycle| are promoted in this example}

It may look as though $ω$-weighted arrows are only useful for
functions while every data type constructor should use linear
arrows. However, the $ω$-weighted arrow is needed for constructor
types as well, as the following data type illustrates:
\begin{code}
  data Bang a where
    Bang :: a → Bang a
\end{code}
The type constructor |Bang| is in fact an encoding of the so-called
\emph{exponential} modality written ${!}$ in linear logic. It is used
to indicate that a linear function returns $ω$-weighted results. For
example:
\begin{code}
  copy :: Bool ⊸ Bang Bool
  copy True = Bang True
  copy False = Bang False
\end{code}
We stress that the above is not the same as the linear identity
function, |id :: Bool ⊸ Bool|. Indeed, |id| conserves the weight of
|Bool|, when |copy| \emph{always} returns an $ω$-weighted value,
regardless of the weight of its argument.

\paragraph{An out of \textsc{gc} queue \textsc{api}}

Linear types make it possible to write memory-safe API for C bindings
that manage out-of-\textsc{gc} data. Indeed, linear bindings must be
used \emph{exactly once}, it means that such a binding is statically
guaranteed to eventually be consumed by the program (no unfreed
garbage) and that the binding cannot be referred to after being
consumed (no use-after-free or free-after-free errors).

Concretely such an \textsc{api} is defined in an ownership-passing
fashion: each operation which do not free the data structure return a
new copy of the data structure (which may be the same as the
original). For instance, pushing in a queue would have the following
type.
\begin{code}
  push :: Queue ⊸ Msg -> Queue
\end{code}
While functions to free the data structure would simply consume the
argument as follows:
\begin{code}
  free :: Queue ⊸ ()
\end{code}

This makes it possible to statically manage long-lived data out
without stressing the garbage collector. A complete \textsc{api} for
queues with random-access deletion is as follows (|Msg| must be
storable to be stored out-of-heap)
\begin{code}
  instance Storable Msg

  alloc   :: (Queue ⊸ Bang a) ⊸ a
  free    :: Queue ⊸ ()
  push    :: Queue ⊸ Msg -> Queue
  delete  :: Queue ⊸ Msg -> Queue
  evict   :: Queue ⊸ Int ⊸ (Queue, Bang (Vector Msg))
\end{code}

There are a few things going on in this \textsc{api}:
\begin{itemize}
\item The function taken as an argument to |alloc| creates a linear
  binding for a |Queue| ensuring that this queue variable \emph{must}
  be used exactly once. The return type of this function is |Bang a|
  ensuring that no linear value can be returned: in particular the
  |Queue| must be consumed.
\item Messages of type |Msg| are copied into regular Haskell values
  (hence managed by the garbage collector) when they are returned by
  |evict|. The hypothesis is that while there is a very large amount
  of messages in the queue, there will always be very few messages
  managed by the garbage collector, therefore imposing a much smaller
  burden on the \textsc{gc}.
\item Because the queue allocated by |alloc| must be consumed before
  the its scope is ended, |free| must be called, and will call the
  foreign procedure responsible for clearing the queue.
\end{itemize}

\todo{Probably add a remark that functional in-place update is not a goal}

\subsection{Guiding fusion}

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
program subject to shortcut fusion. Additionally, it is not uncommon
for a compiler to even introduce sharing where the programmer doesn't
expect it, effectively creating a memory leak
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

\paragraph{Semantics of the optimiser}

In order to perform inlining and fusion, \textsc{ghc}'s optimiser perform a
cardinality analysis. Indeed, blindly inlining functions may worsen
the performance of a program. This is illustrated by the following
example take from \textcite{dominguez_parafusion_2006} illustrates the
issue:
\begin{code}
  tails :: [a] -> [[a]]
  tails (_ : xs) = xs : tails xs
  tails [] = []

  map :: (a -> b) -> [a] -> [b]
  map f (x : xs) = f x : map f xs
  map _ [] = []
\end{code}
We have that ~force . tails . map (+1)~ consumes memory linearly in
the size of its input whereas the fused
\begin{code}
  tailsmap :: (a -> b) -> [a] -> [[b]]
  tailsmap f (_ : xs) = map f xs : tailsmap f xs
  tailsmap _ [] = []
\end{code}
makes ~force . tailsmap (+1)~  consumes memory quadratically in the
size of its input.

This cardinality analysis is performed by the optimiser on a
best-effort basis. Which means that a programmer has no control over
when the optimisation will be performed and must try its best to fall
in the good grace of the optimiser. As a consequence the performance
of a program may change significantly in an unpredictable manner.

Using linear types to make sure that the optimiser inlines a function
makes it possible to consider fusing optimisation part of the
semantics of the compiler, imposing that the optimiser honours the
intent of the programmer.

\subsection{Prompt deallocation of cons cells}

To go even further the run-time system can be modified to allow
regular Haskell data (which we will refer as \emph{cons cells}), as
opposed to just primitive data, to reside out of the \textsc{gc} heap
as long as it has been allocated by a linear binding.

With such a modification the queue \textsc{api} from \fref{sec:ffi}
can be implemented directly in Haskell rather than be implemented in C
and merely bound via the foreign function interface. Furthermore, we
can arrange the messages returned by the queue to also reside out of
the \textsc{gc} heap; this way, using the queue would entail zero
\textsc{gc} allocation, therefore would never trigger a \textsc{gc}
collection and have extremely low latency.

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
    Matrix Int Int Int Int

  -- With a bit of care, matrix multiplication can be implemented
  -- linearly. This assumes a linear implementation of |(+)| and |(*)|
  -- for integers.
  multMatrix : Matrix ⊸ Matrix ⊸ Matrix
  mult (Matrix x11 x12 x21 x22) (Matrix y11 y12 y21 y22) =
      Matrix
       (x11*y11+x12*y21)
       (x11*y12+x12*y22)
       (x21*y11+x22*y21)
       (x21*y12+x22*y22)
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

Because all the allocation of matrices happen in linear let-bindings,
it is possible to allocate all of them out of the \textsc{gc} heap,
\emph{as long as the result is used linearly}. To understand where
this limitation comes from, consider the following example:
\begin{code}
  forget :: Int -> ()
  forget _ = ()

  forget (fib 42)
\end{code}
Here |fib 42| is promoted to weight $ω$ because |42|, being a literal,
has weight $ω$. But then |fib 42| is dropped without being forced so
it need to be garbage collected, as well as every value in the
closure. A partial evaluation of |fib 42| may cause the intermediate
matrices to be pointed to by the closure, therefore they need to be
garbage collected and cannot be allocated out of the \textsc{gc}
heap. A similar issue occurs when the return value of |fib 42| is used
several times.

To ensure that the linearly-bound matrices are allocated on the
\textsc{gc} heap, one must ensure that the result of |fib| is copied
to the \textsc{gc} heap at the end of the computation. This is done in
two part. First the result is wrapped in a |Bang| using the |copy|
function (|Int|, like every data type, implements this method):
\begin{code}
  copy :: Int ⊸ Bang Int
\end{code}
Then, the |Bang| constructor is forced using a pattern-matching. This
has the effect of producing an |Int| closure of weight $ω$, hence on
the \textsc{gc} heap. The run-time system is allowed to assume that no
linear value are still live at this point (a $ω$-weighted value is
statically guaranteed to have no reference to linear bindings)
therefore that they can all be allocated, and managed, out of the
\textsc{gc} heap.

Revisiting our |forget| example, we can write:
\begin{code}
  case copy (fib 42) of
    Bang x -> forget x
\end{code}
In this expression, all the intermediate matrices can safely be
allocated out of the \textsc{gc} heap and be deallocated by
the run-time system at the point where they are consumed. The downside
being that we will run |fib 42| to completion even if the result is
not actually needed.

\printbibliography

\end{document}
