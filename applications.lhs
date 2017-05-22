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
|Unrestricted b|.\unsure{Arnaud: I'm not sure that we can implement
  a generic |borrow| without breaking some abstractions. It may be
  preferable to use a type class |Borrowable|.}

The correctness of this proposal has yet to be verified.

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
  withFile :: FilePath -> (FileHandle -> IO a) -> IO a
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
  withFile :: FilePath -> (forall s. FileHandle s -> IO s a) -> IO t a
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

Example with cloud-haskell+file

\section{|Unrestricted| as a |newtype|}

\section{Linear IO}
\label{sec:linear-io}

\subsection{Monomorphic linear IO}

\subsection{Multiplicity-polymorphic IO}

\section{Protocols: Cloud Haskell}
\label{sec:prot-cloud-hask}

\emph{To be done}

\section{Protocols: Inline-Java}
\label{sec:prot-inline-java}

\emph{To be done}

\end{document}

%  LocalWords:  aliasable deallocate deallocating GC deallocation
%  LocalWords:  affine monad
