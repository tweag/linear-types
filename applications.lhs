% -*- latex -*-
% Created 2016-09-15 tor 14:09
\documentclass[11pt]{article}
%include polycode.fmt
%format .         = ". "
%format forall a         = "∀" a
%format _ (a)         = "_{" a "}"
%format ω = "\omega"
%format β = "\beta"
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

\newcommand\HaskeLL{Hask-LL}
\newcommand\calc{{\ensuremath{λ^q}}}

\author{Arnaud Spiwack}
\title{Designing linear types applications}
\hypersetup{pdflang={English}}

\begin{document}

\maketitle

\begin{abstract}
  This documents list potential applications of linear types and how
  these applications are handled in the \HaskeLL{} design.

  Status: draft
\end{abstract}

\section{Preamble: introducing linear values}
\label{sec:preambl-intr-line}

The purpose of this section is to establish terminology.

Because of promotion, it is not completely direct to write a function
which returns a linear value (linear in that it cannot be passed to an
unrestricted function). There are two ways to achieve this goal.

\begin{description}
\item[Scoped introduction] We can introduce a linear value by making
  it an argument of a function, the \emph{scope} of the value:
  \begin{code}
    scoped :: Arg ⊸ (L ⊸ R) ⊸ R
  \end{code}
  Within the scope, |L| is understood as a linear value by the
  type-checker. It is often necessary, for safety, that |L| doesn't
  escape the scope, which imposes restrictions on the return type
  |R|. It can be |()| in which case no value can escape the scope. It
  is often preferable to choose |Unrestricted R'| for an arbitrary
  |R'|: the typing rule for |Unrestricted| ensures that no linear
  value can escape\footnote{In either case, the |scoped| function must
    be strict, otherwise |L| could escape in the thunk of type |R| and
    promotion of this thunk would be unsafe}.
\item[Source of linearity] If you already have a value which is
  guaranteed to be linear (\emph{e.g.} the |World| token in |IO|),
  then this variable will ``contaminate'' the values returned by any
  function taking it as an argument. That is, in:
  \begin{code}
    gen :: World ⊸ L
  \end{code}
  |L| will be a linear value. However |World| will be consumed, so a
  more realist type for |gen| would be
  \begin{code}
    gen :: World ⊸ (World,L)
  \end{code}
  In other worlds, if |IO_l| is the linear |IO| monad (see
  \fref{sec:linear-io}), then |gen| would have this type.
  \begin{code}
    gen :: IO_l L
  \end{code}
  Of course, it works with sources of linearity other than |World|.
\end{description}

Remark that while scoped introduction has the power of summoning
linear values out of nothing, without any sequencing whatsoever, it
will add a frame on the stack, nesting too many scoped introductions
could be costly for efficiency.

\section{In-place update}

In-place update with a pure type is not the primary goal of the \HaskeLL{}
design, however, it can be handled gracefully and illustrates several
aspects of \HaskeLL{}.

\subsection{In-place array API}

We assume given either method of generating a new, linear, array value
as in \fref{sec:preambl-intr-line}. For the sake of simplicity we will
assume that the data stored into an array, is unrestricted. This
restriction is lifted in \fref{sec:arrays-linear-values}.

The following \textsc{api} make it possible to update an array in
place without using the |ST| monad.

\begin{code}
  type Array a
  type Index -- type of indices in an array

  set :: Index -> Array a ⊸ a -> Array a
  get :: Index -> Array a ⊸ (Array a, a)

  -- Consumes the array when it is not needed anymore.
  drop :: Array a ⊸ ()
\end{code}

The advantage over |ST| is that instructions related to different arrays
need not be sequenced with one another, only instructions on the same
array must be. This leaves more options for optimisation.

\subsection{Freezing arrays}

A simple addition which can be made to the mutable array \verb|API| is
the ability to yield an immutable array. The mutable array is
guaranteed not to be accessible anymore, so this is an entirely safe
construction\unsure{Arnaud: I don't think this is quite possible with
  |ST| or |IO|. I suppose we could do something in |ST| when exiting
  the |runST| scope.}.

\improvement{Arnaud: should be \verb+'Mutable+ and \verb+'Frozen+ below, but
  it seems to confuse \verb+lhs2tex+}
\begin{code}
  type Array a = Array_c Mutable a
  type Array_c (c :: Mutability) a
  type Mutability = Mutable | Frozen

  freeze :: Index -> Array c a ⊸ Unrestricted (Array Frozen a)

  -- Generalises the type from the purely mutable API.
  get :: Index -> Array_c c a ⊸ (Array c a, a)

  -- The traditional get function can be implemented in terms of |get|
  -- because |get i a| is promoted.
  get' :: Index -> Array a -> a
  get' i a = snd (get i a)
\end{code}

\subsection{Fork-join algorithms on arrays}
\label{sec:fork-join-algorithms}

The typical example of fork-join, in-place, algorithms on array is
quick-sort, where the array is split around the pivot and
``reassembled'' in place when sorting both halves has completed.

Aside on Rust: Rust supports fork-join in place algorithms with a function
\verb+split_at_mut+\footnote{\url{https://doc.rust-lang.org/std/primitive.slice.html\#method.split_at_mut}}
with the following type:
\begin{verbatim}
fn split_at_mut(&mut self, mid: usize) -> (&mut [T], &mut [T])
\end{verbatim}
It takes two, non-overlapping, non-aliasable references to an
array. Such references, in Rust, have a limited lifetime (their
lifetime is bound to a scope enclosing the call to
\verb+split_at_mut+). When their lifetime is over, the original array
is available again (for mutation or otherwise).

To replicate this semantic, with linear types, we need to give an
explicit scope in which the halves are valid:
\begin{code}
  split_at :: Array a ⊸ (Array a ⊸ Array a ⊸ Unrestricted b) ⊸ (Array a, Unrestricted b)
\end{code}
Note that in |split_at array scope|, |array| is not available in
|scope| or in the continuation of |split_at|, the original, modified,
array must be returned at the end of the call. Like with scoped
introduction (see \ref{sec:preambl-intr-line}), |scope| returns an
|Unrestricted b| to ensure that no the halves don't escape their
scope.

\subsection{Arrays of linear values}
\label{sec:arrays-linear-values}

We can extend mutable arrays to have linear elements (in particular
other mutable arrays) with the following \textsc{api}. Note that
|modify| generalised both |set| and |get|.

\begin{code}
  type Array_l a
  type Array a = Array_l (Unrestricted a)

  modify :: Index -> Array_l a ⊸ (a⊸(a, b)) ⊸ (Array_l a, b)
\end{code}

Note: an |Array_l a| cannot, in general, be frozen: its elements need
to be frozen first\unsure{Arnaud: it's not terribly important, but,
  because of this, I'm not sure how to make |Mutability| polymorphic
  code with |Array_l|}.

\section{Borrowing}
\label{sec:borrowing}

When the purpose is simply to scope the usage of an immutable value
that needs to be explicitly deallocated (such as an immutable value in
a foreign heap, such as \fref{sec:prot-inline-java}), using linear
types and state-passing style of values may be too heavyweight for
practical applications.

It is in part for this reason that Rust introduces borrowing. Borrowing a
value gives a reference with a scoped life-time to a value without
relinquishing ownership.

While we cannot seem to recover all of Rust syntactic convenience, we
can extend \HaskeLL{} with a notion of borrowing. Remember that,
contrary to Rust, the \HaskeLL{} programmer does not need to track
ownership in types for every value. So we expect that the
less convenient syntax will be perfectly acceptable in practice.

To implement borrowing, we can introduce a new multiplicity: $β$ (for
\emph{borrowed}). Variables of multiplicity $β$ would support
contraction and weakening, like with $ω$. However, $β<ω$\footnote{Also
  $β$ becomes the new least upper bound of $0$ and $1$ and $1+1=β$}.

Borrowed variables are introduced with scoped introduction (see
\fref{sec:preambl-intr-line}) with a function:
\begin{code}
  borrow :: a ⊸ (a -> _ β Unrestricted b) ⊸ (a, Unrestricted b)
\end{code}
The |borrow| function is similar to the |split_at| function from
\fref{sec:fork-join-algorithms}, except that the introduced value has
multiplicity $β$, hence can be used any number of times in the scope
(including $0$). The borrowed value cannot escape its scope since
$β<ω$ hence no borrowed value can be referred to in a value of type
|Unrestricted b|.

The correctness of this proposal has yet to be verified.

This type is a bit too general. With a generic |borrow| function it
would be hard to give a meaning to |close f| for a borrowed file
|f|. Plus, there is no way to prevent |freeze a| for a borrowed
(mutable) array |a| (which is unsound).

The proper way would probably be to have a typeclass:
\begin{code}
  class Borrow a where
    type Borrowed a
    borrow :: a ⊸ (Borrowed a -> _ β Unrestricted b) ⊸ (a, Unrestricted b)
\end{code}
We may want to provide a default implementation with an abstract type
\begin{code}
  newtype StdBorrowed a -- abstracted: = StdBorrowed a
\end{code}
So that it can be automatically derived with |DeriveAnyClass| (or an
empty instance)

\subsection{Exploring a generic API}

But it's not clear how to give a \textsc{api} such that it can be used
to limit the power of borrowed object (a |StdBorrowed Handle| can't be
closed, and a |StdBorrowed Array| can't be frozen) but allow library
writers to define functions which consume |StdBorrowed| without
depending on some |unsafeUnborrow| projection.

A fundamental difference between this flavour of borrowing and Rust's
is that our borrowed values are \emph{easier} to use than linear
values (in that everywhere a linear value may be used, a borrowed
value of the same type may too). Whereas in Rust, it is, in a sense,
the opposite.

As a result, Rust marks borrowed value as type \verb+&a+ and
unrestricted values with the type \verb|RC<a>|. We may want to do the
opposite: we may want to let the unrestricted type be unmarked and
mark the type that can't be unrestricted:
\begin{code}
  -- It is a contract violation to produce a value of type |Owned a|
  -- with multiplicity different from 1
  newtype Owned a = unsafeOwned { unOwn :: a }
  -- It is a contract violation to produce a value of type |Borrowed a|
  -- with multiplicity different from β
  newtype Borrowed a = unsafeBorrowed { unBorrow :: a }
\end{code}
None of the two types above are abstract. It's just conventional to
use them this way, so that library owners can use |unsafeOwn| when
they guarantee that a value will not be aliased. For instance. We can
use an instance (or default implementation, whichever is found to be
best):

\begin{code}
  instance Borrow (Owned a) where
    type Borrowed a = Borrowed a -- uhm, two |Borrowed|, but aspiwack
                                 -- is too lazy to think of a second
                                 -- one.
    borrow (Owned a) scope =
      -- It may be unsafe not to be strict because, otherwise, |a| may be
      -- deallocated before the closure |scope (unsafeBorrow a)| is forced.
      case scope (unsafeBorrow a) of
        Unrestricted b -> (unsafeOwn a, Unrestricted b)
\end{code}

\section{Exceptions}

Haskell exceptions are of three kinds:
\begin{description}
\item[Imprecise exceptions] typically represent programming errors
  (such as division by zero). They are really rare. They can be
  recovered from, but this is meant mostly for clean-up.
\item[Precise exceptions] thrown by I/O operations. Typically failures
  from outside of Haskell, such as ``too many handles'' on a
  database. We usually want to handle such exceptions properly as part
  of the program logic.
\item[Asynchronous exceptions] thrown by another thread in order to
  kill the current thread (\emph{e.g.} to cancel an |Async|). These
  are rather frequent in some programs.\unsure{I don't know whether we
  usually want to catch such exceptions. Probably just for clean up
  like imprecise exceptions?}
\end{description}

Mixing exceptions and linear types poses two kinds of problems:
\begin{itemize}
\item Since computations are interrupted, linear variables which
  should be consumed once may end up not being consumed at all. When
  memory safety depends on linear variables being properly consumed
  (such as a file handle which must be closed), memory safety must be
  ensured in presence of exceptions.
\item Catching and handling exceptions in presence of linear value is
  significantly harder. Let us delay this discussion until
  \fref{sec:catching-exceptions}.
\end{itemize}

On the other hand, we will have sometimes types which can be inhabited
both with unrestricted and non-unrestricted values such as the type of
Java references in \fref{sec:prot-inline-java} (in this case it would
typically be borrowed or unrestricted). The same functions are
applicable to both multiplicity, and thanks to promotion, will return
unrestricted values if their argument is unrestricted, so that such
values \emph{can} escape the scope of a borrowed function, which is
exactly the desired behaviour.

\subsection{Terminators}

One possible solution to keeping memory safety in presence of
exceptions is to attach a terminator to each resource that needs to be
freed when they are left dangling due to an exception.

The resources will still be freed promptly by the programmer, but in
case of exception, they will become orphan and the terminator will
eventually kick in.

Relying on the GC to free scarce resources can be very wasteful if
many exceptions happen: if the program does not allocate much in the
GC, then it may take seconds, or more, for the scarce resource to be
freed during which the number of open resources may very well reach
the maximum allowed.

The gain is that this works out of the box with both allocation styles
from \ref{sec:preambl-intr-line}.

\subsection{Scoped resources}

If we restrict our attention to scoped introduction. Then we don't
need terminators at all: upon leaving the scope where the resource was
introduced, we can deallocate any stray resources.

That is the function responsible of allocating the resource (like
|scoped| in \fref{sec:preambl-intr-line}) also installs a resource
handler responsible with deallocating the resource in case of
exception.

\subsection{Advantage of linearity over simple scopes}

Haskell already features a function
\begin{code}
  withFile :: FilePath -> (Handle -> IO a) -> IO a
\end{code}

If all of our allocations are to be scoped, then why bother with
linearity at all, we could just use functions such as |withFile|. It
is worth noting that |withFile| is not actually safe in that
\begin{code}
  withFile path (fun h -> h)
\end{code}
is type-correct, but the file handle survives beyond being closed.

Of course, this example is blatantly wrong and the conscious
programmer is unlikely to make such a mistake. It is much easier,
however, to inadvertently let |h| survive in a closure. Running such a
closure would result in a use-after-free error. Linearity prevents
such a mistake from happening.

\subsection{Advantage of linearity over affinity}

One may, then, wonder what the point of using linear types, rather than
affine types, is: indeed, we may just let the |scoped| function do the
deallocation in every case, not only in exceptional cases.

The advantage of linear types is that it makes it easier to have early
deallocation. It means that scope can be long lived without risk of
resource leaks. There are also other kinds of protocol where the final
consumption of a value is not, typically, a mere deallocation (see
\fref{sec:prot-cloud-hask}).

Linear types are slightly more general, but if the need for affine
types is pressing, it is just a matter of adding an affine
multiplicity in \HaskeLL{}.

\subsection{Advantage of linear types over ST-style regions}

There is an instance, in Haskell, of a safe scoped computation: the
|ST| monad. Could we use it instead of linearity for scoped
introduction? We could, but at a significant cost: if |withFile| had
type\footnote{Note that, just like in the case of |ST| we need to tag
  the ambient monad with the region type, otherwise there is nothing
  preventing an escaping closure to be run in another environment. We
  need not actually modify |IO| though.}
\begin{code}
  withFile :: FilePath -> (forall s. Handle s -> IO s a) -> IO t a
\end{code}
then writing a code with two files becomes impossible. So we need to
have functions to transfer files to sub-regions. This is quickly very
tedious.

At least it is in current Haskell. But maybe we could change the type
system to handle regions better. What would it look like? It would
probably look a lot like Rust: in Rust every reference is tagged with
a life-time and an elaborate life-time analysis decides which scope to
attach references to. The scope is then elaborated to deallocate the
reference when required. In the case of Haskell we would only need to
tag variables that have to be scoped, but the order induced by
sub-regions would force adding a sort of sub-typing discipline in the
type inference. It is more complex than adding linear types, even
without taking the elaboration into account.

With linear types, we could also design a safer |ResourceT|. The
|runResourceT| function is subject to the same safety issue as
|withFile|. It differs in that |runResourceT| doesn't introduce
resources, instead allocating resources allocates a terminator to the
scope of |runResourceT| and resources are deallocated in bulk when the
scope is exiting.

From the point of view of linearity, |runResourceT| can be seen as
introducing a source of linearity, in the form of the terminator
table. Allocating resources as linear variable would make it
impossible for values to escape the scope. It would also be possible
to allocate resources as borrowed variables (see \fref{sec:borrowing})
depending on the usage.

This is harder to do with life-times as it would require that any
potential resource has a life-time parameter. Whereas with \HaskeLL,
it can be just an abstraction provided on top of a regular,
memory-unsafe, \textsc{api}

\subsection{Catching exceptions}
\label{sec:catching-exceptions}

The best type we can give to the |catch| function is:
\begin{code}
  catch :: Exception e => IO a ⊸ (e -> IO a) -> IO a
\end{code}
Specifically the handler is unrestricted: it cannot contain references
to a linear value. The reason is rather clear: the handler will
typically not be run, so it will not be able to consume any of its
linear variables.

To see how it can be a problem consider the following
cloud-haskell-like \textsc{api}, in source-of-linearity style:

\begin{code}
  sendChan     :: SendPort a ⊸ a ⊸ IO ()
  receiveChan  :: ReceivePort a ⊸ IO_l a
\end{code}

In other words, a |ReceivePort| yields exactly one value, and a
|SendPort| sends exactly one value (see \ref{sec:prot-cloud-hask} for
more on protocols).

We can write the following program. It read:
\begin{code}
  do
    (path,replyPort) <- receiveChan port
    h <- openFile
    writeFile h ``lorem ipsum''
    sendChan replyPort Ack
\end{code}

The disk if full and the |writeFile| operation fail, in which we may want to return a |DiskFull| message
to the |replyPort| rather than crashing:

\begin{code}
  do
    (path,replyPort) <- receiveChan port
    h <- openFile
    write `catch` handleDiskFull
  where
    write = do
      writeFile h ``lorem ipsum''
      sendChan replyPort Ack
    handleDiskFull _exception = do
      sendChan replyPort DiskFull
\end{code}

However, this is not well-typed because |handleDiskFull| mentions
|replyPort|, which is linear. There does not seem to be a way around
this limitation so we will need to push the error handling closer to
the source of failure and use an explicit |Either| type\footnote{For
  the sake of comparison, Rust has no equivalent to precise exception,
  potentially failing functions will return a value of type
  \verb+Result+ which is similar to |Either|.}
\begin{code}
  do
    (path,replyPort) <- receiveChan port
    h <- openFile
    res <- write `catch` handleDiskFull
    case res of
      Left () -> sendChan replyPort Ack
      Right _exception -> sendChan replyPort DiskFull
  where
    write = do
      writeFile h "lorem ipsum"
      return (Left ())
    handleDiskFull exception = return (Right Exception)
\end{code}

Example with cloud-haskell+file

\section{|Unrestricted| as a |newtype|}

\begin{code}
  newtype Unrestricted a = Unrestricted :: a -> Unrestricted a
\end{code}

Is unsafe because pattern-matching on an |Unrestricted a| is lazy in
Haskell. Because the projection is unrestricted, the entire thunk may
be dropped, which violates the condition that linear values must be
consumed (if there is a linear value in the closure).

Example:
\begin{code}
  type Resource -- some kind of resource
  move :: Resource ⊸ Unrestricted Resource  -- moves the resource into
                                             -- the GC heap

  faulty :: Resource ⊸ ()
  faulty r =
    case move r of
      Unrestricted _ -> ()
\end{code}
In this example, if the |case| is strict, then |move| is actually run
and the resource is copied from the linear heap to the GC heap. But if
the case is transformed into a lazy cast, then the resource will be
left, inaccessible, in the linear heap (memory leak).

It may be that laziness prevents use-after-free errors, though.

It is ok to return an |Unrestricted| in sufficiently strict
contexts. For instance, the primitives of type |World ⊸
(World,Unrestricted a)| can be correct because the |IO| runner will
always run the action. As long as the action makes sure that it never
returns a thunk.

The story needs to be polished with such types.

\section{Linear IO}
\label{sec:linear-io}

\subsection{Monomorphic linear IO}

\begin{code}
  type IO_l  a  = World ⊸ (World, a)
  type IO    a  = IO_l (Unrestricted a)
\end{code}

Two bind functions:
\begin{code}
  (>>=)   :: IO a    ⊸ (a -> IO_l b) ⊸ IO_l b
  (>>==)  :: IO_l a  ⊸ (a ⊸ IO_l b) ⊸ IO_l b
\end{code}
(the former is definable in terms of the former)

\emph{To be expanded}

\subsection{Multiplicity-polymorphic IO}

\begin{code}
  newtype Multiplicity p a where Multiplicity :: a -> _ p Multiplicity p a
  type IO p a = IO_l (Multiplicity p a)

  return  :: a -> _ p IO p a
  (>>=)   :: IO p a ⊸ (a -> _ p IO q a) ⊸ IO q a
\end{code}

\emph{To be expanded}

\section{Protocols: Cloud Haskell}
\label{sec:prot-cloud-hask}

Consider the following API where channel ports can always be used
exactly once.

\begin{code}
  -- For simplicity, we ignore type-class constraint on sending things

  type SendPort a
  type ReceivePort a

  newChan :: IO_l (SendPort a, ReceivePort a)
  send :: SendPort a ⊸ a -> IO ()
  receiveChan :: Receiveport a ⊸ IO_l a
\end{code}

Then we can encode protocols. First we need a polarity-changing type
\begin{code}
  type N a = SendPort a
\end{code}
Each change of polarity reflects a switch regarding who is responsible for a
particular action.

For instance, a server performing a multiplication (uses a linear
version of |async|):
\begin{code}
  type P = (Int,Int,N Int)

  server :: IO_l (N P, Async ())
  server = do
    (sendPort,receivePort) <- newChan
    ack <- async $ do
      (n,p,r) <- receive receivePort
      send r (n*p)
    return (sendPort,ack)

  client :: N P ⊸ IO_l Int
  client server = do
    (sendPort,receivePort) <- newChan
    res <- async $ receive receivePort
    send server (42,57,sendPort)
    wait res

  main :: IO ()
  main = do
    (s,done) <- server
    res <- client s
    wait done
    putStrLn (show res)
\end{code} % $ (work-around syntax highlighting bug)

Here is an example with more polarity changes\footnote{See \url{http://www.tweag.io/posts/2017-03-13-linear-types.html}}:
\begin{code}
data Number = Singular | Plural
type P = (Int, N (Number, N (String, N String)))

server :: IO_l (N P)
server = do
    (sendPort,ReceivePort) <- newChan
    ack <- async $ do
      (n, k) <- receive receivePort
      (s, r) <- newChan
      ack' <- async $ do
        (apples, k') <- receive r
        send k' ("I have " ++ show n ++ apples)
      send k (num, s)
      wait ack'

      where
       num = if n == 1 then Singular else Plural

client :: N P ⊸ IO_l String
client k = do
    (s, r) <- newChan
    rest <- async $ do
      (num, k') <- receive r
      (s', r') <- newChan
      rest <- async $ receive r'
      let apples
           | Singular <- num = "apple"
           | Plural <- num = "apples"
      send k' (apples, s')
      send k (42,send s)
      wait rest
\end{code} % $ (work-around syntax highlighting bug)

\section{Protocols: Inline-Java}
\label{sec:prot-inline-java}

\texttt{inline-java} is a project that aims to achieve seamless
interoperation between Haskell and the JVM. Haskell objects live in
the Haskell heap, Java objects live in the JVM heap. But both heaps
live in the same address space and objects in either heap is permitted
to hold references to objects in the other heap.

Interaction with the JVM is done via the JVM's equivalent of the FFI,
called the JNI. The JNI makes it possible for foreign languages to
create two types of references to Java objects:
\begin{description}
\item[global references] a global reference is like a regular |Ptr| to
  a C struct: it can be used from any thread and its lifetime is
  managed entirely manually (need to call |DeleteGlobalRef()|
  explicitly eventually).
\item[local references] a local reference is meant to be short-lived.
  It only survives the scope of the current native call. As soon as
  the Haskell function at the top of the call stack returns to a Java
  function that called it, all local references created in that call
  frame are automatically disposed of. Local references are only valid
  in the current thread. They cannot be shared.
\end{description}
Our strategy in \texttt{inline-java} is to leave managing global
references to the Haskell GC. That way, there is a good chance global
references will eventually be disposed of it they become unreachable.

Local references are a lot harder. We can't have the GC manage them,
because these references are only valid in the thread that created
them. Furthermore, we {\em do} need to free them manually sometimes,
because holding onto an object until the end of the current call frame
has been observed in real world applications time and time again to be
far too long.

Yet programmers will want to create {\em local} references wherever
possible, instead of global ones, because local references are cheaper
to create. Moreover, since the Haskell GC is unaware of the GC
pressure on the JVM heap, it's hard to ensure a timely release of
stale references held Haskell side to JVM objects (without any GC
pressure Haskell side, the Haskell GC might not run at all for a very
long time even as the JVM heap is filling up to the brim).

The central question is:
\begin{quote}
  \em How can we free local references early yet guarantee memory safety?
\end{quote}

This is where linear types can help. We could organise things as
follows:

\begin{enumerate}
\item local references are always linear. Being handed a local
  reference comes with the obligation to dispose of it eventually.
\item global references are never linear. They are entirely managed by
  the GC, via finalizers that deletes the global reference when it
  becomes unreachable, just like any other Haskell object.
\end{enumerate}

Now, the issue is that we do want to leverage borrowing. Plain linear
types are too cumbersome. A common pattern is to {\em hide} local
references behind newtype wrappers, so that Java objects look like an
abstract ADT's on the Haskell side. We want to pass these ADT's to
functions and have the functions manipulate them with little fuss.
With plain linear types, any access to a Java object via a local
reference requires producing a new one. These references then have to
be threaded explictly through computations (aka state-passing style).
With borrowing, one would be able freely query objects through the
same local reference within a single static scope.

\section{Miscellaneous examples}

\subsection{Counting with branches}

Linear types can also help write correct pure programs, in a
way similar to parametric polymorphism

Suppose:
\begin{code}
  class Sized a where
    size :: a -> Int

  data Tree a = Bin (Tree a) (Tree a) | Leaf a
\end{code}

We want:
\begin{code}
  sizeTree :: Size a => Int -> a -> Int
  sizeTree i (Bin l r) = sizeTree (sizeTree i r) l
  sizeTree i (Leaf x) = i + size x
\end{code}

If we forget |i| somewhere, like |sizeTree i (Leaf x) = size x| we
would get a warning.

However:
\begin{code}
  data Tree' a = Bin (Tree a) (Tree a) | Leaf (Maybe a)

  sizeTree :: Size a => Int -> a -> Int
  sizeTree i (Bin l r) = sizeTree (sizeTree i r) l
  sizeTree i (Leaf x) =
    case x with
      Just x -> i + size x
      Nothing -> i
\end{code}

If we write |Just x -> size x| instead. Then no warning is triggered.

If we choose
\begin{code}
  sizeTree :: Size a => Int ⊸ a -> Int
\end{code}
Then such an error would be rejected.

Remark: supposing that |+| has a linear type.

\end{document}

%  LocalWords:  aliasable deallocate deallocating GC deallocation
%  LocalWords:  affine monad
