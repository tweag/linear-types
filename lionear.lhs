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

\newcommand\HaskeLL{Hask-LL}
\newcommand\calc{{\ensuremath{λ^q}}}

\author{Arnaud Spiwack}
\newcommand{\subtitle}{The essence of world-passing style}
\title{Linearising the awkward squad\\\small\subtitle}
\hypersetup{pdflang={English}}

\begin{document}

\maketitle

\begin{abstract}
  We demonstrate how it is possible to justify program transformations
  on linearly typed programming language with effects.
\end{abstract}

\begin{description}
\item[Remark] \it This is still very much a draft. For the moment it
  ignores laziness, non termination and exceptions.
\end{description}

\section{Categorical models of linear types}
\label{sec:category-linear}

\begin{itemize}
\item Models of linear types are symmetric monoidal categories (this
  justifies $βη$ rules) with a few extra conditions
\item \textcite{benton_monad-linear_1996} show that such monoidal
  categories arise from any (strong) commutative monad (indeed they
  are equivalent to strong commutative monads on a cartesian closed
  category)
\end{itemize}

\section{Modelling linear types and effects}

As noticed in \fref{sec:category-linear}, we can reduce the problem of
giving a semantics to linearly typed $λ$-calculus to crafting a
commutative monad.

Let us assume that our pure functions are simply functions between
sets. That is, our base cartesian closed category will be the category
of sets.

The monad $\mathfrak{E}$ will be a ``writer'' monad, that is a monad
of the form $(A,\mathbf{M})$ for a monoid $\mathbf{M}$. Such a monad
is commutative whenever $\mathbf{M}$ is a commutative
monoid\todo{Justify}.

For $\mathbf{M}$ we choose some model of concurrency, such as sets of
traces, or \textsc{ccs}. Specifically, it is a partial map from a set
of thread names to such a model\footnote{It means, rather unusually,
  that the threads are not single threaded. It will probably be more
  elegant, actually, to have a partial composition and have
  inconsistent program have a faulty semantics.}. The product of that
monoid is \emph{parallel} composition, such that common prefixes of threads
are merged (\emph{i.e.} $(t↦ab)+(t↦ac, u↦d) = (t↦a(b+c), u↦d)$).

\section{World-passing style}

Of course, we are not ultimately all that interested in commutative
effects. A world-passing monad on the linear category is the mechanism
which will make it possible to sequence effects.

The main remark to keep in mind is that the available effects in the
monoidal category are quite omnipotent. They can act on any threads,
or all of them at the same time, they also can return arbitrary long
sequenced threads. It's only when they are \emph{composed} that they
are composed in parallel. This should be understood as ``pure'' linear
functions being capable of effects, but they can be reordered
arbitrarily according to $βη$-equivalence\footnote{this is modelled as
concurrency, but we expect the implementation to be actually
sequential, it's only that the compiler is allowed to change the order
in which the effects are actually performed. Compared to an actual
thread-based implementation, this is much more efficient, but loses
any notion of fairness, this should be kept in mind when designing
linear interfaces}. So we have very expressive primitive, but very
concurrent composition.

So, what's next? Let |World| be the type of traces with a
distinguished thread (dubbed \emph{the current thread}). A |World|
should be seen as identifying what thread is running the computation
as well as containing the history of the entire world. Primitives of
type |World ⊸ World| (or, more generally |World ⊸ (World, a)|) can
\emph{extend} the history of the |World|, mirroring the operational
semantics of \textcite{peyton_jones_awkward-squad_1999}\todo{With a
  bit of work, we should be able to make it \emph{exactly} the same as the
  operational semantics. Regarding exceptions, though, they would
  probably have to be part of the commutative monad, while |catch|
  would, I assume, still be a primitive in the world-passing style
  view. So they would look a bit different.}.

So actually effectful functions appear as pure functions without
compromising safety.

This also makes it possible to represent ``pieces'' of the world which
are loosely ordered with each other. For instance, one may imagine an
array with signature:
\begin{code}
  newArray  :: World ⊸ List a ⊸ Array a
  map       :: (a ⊸ b) -> Array a ⊸ Array b
  fold      :: (a ⊸ b -> b) -> Array a ⊸ b -> b
\end{code}
Such that |map| is implemented as in-place update. The semantic of the
type |Array a| would be, together with an actual array of |a|-s, a
history of the world, and a current thread which is unique to that
array.

Another example would be |malloc|-d data-structures with a pure
interface.

\printbibliography

\end{document}

%  LocalWords:  monad cartesian monoidal effectful
