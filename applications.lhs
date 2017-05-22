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

\section{Exceptions}

\subsection{Terminators}

\subsection{Scoped resources}

\subsection{Advantage of linear types over ST-style regions}

Todo: best region system = rust.

Safer |ResourceT|

\subsection{Catching exceptions}

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

%  LocalWords:  aliasable
