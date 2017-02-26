% -*- latex -*-

% (1) Horrible, terrible, 1 column format.  111 characters in a line; bad on the eyes.
\documentclass[acmlarge,dvipsnames,natbib,anonymous,review]{acmart}

% (2) More or less the good old lovable format.  For use while writing/printing.
% \documentclass[sigplan,dvipsnames,10pt,review,anonymous]{acmart}\settopmatter{printfolios=true}

\usepackage[mathletters]{ucs}
\usepackage[utf8x]{inputenc}
%include polycode.fmt
%format .         = ". "
%format forall a         = "∀" a
%format _ (a)         = "_{" a "}"
%format ω = "\omega"
%format π = "\pi"
%format ρ = "\rho"
%format ⅋ = "\parr"
%subst keyword a = "\mathsf{" a "}"
%format bigSpace = "\hspace{2cm}"
%format allocT = "alloc_T"
%format freeT = "free_T"
%format copyT = "copy_T"
%format __ = "\_"
% \usepackage[backend=biber,citestyle=authoryear,style=alphabetic]{biblatex}
\usepackage{natbib}
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
\usepackage{cmll}
\usepackage{capt-of}
\usepackage{hyperref}
\hypersetup{
    colorlinks,
    linkcolor={red!50!black},
    citecolor={blue!50!black},
    urlcolor={blue!80!black}
  }
\usepackage{mathpartir}
% \usepackage{fontspec}
% \usepackage{unicode-math}
\usepackage[plain]{fancyref}
\def\frefsecname{Section}
\def\freffigname{Figure}
\def\frefdefname{Definition}
\def\Frefdefname{Definition}
\def\freflemname{Lemma}
\def\Freflemname{Lemma}
\def\fancyrefdeflabelprefix{def}
\frefformat{plain}{\fancyrefdeflabelprefix}{{\frefdefname}\fancyrefdefaultspacing#1}
\Frefformat{plain}{\fancyrefdeflabelprefix}{{\Frefdefname}\fancyrefdefaultspacing#1}
\def\fancyreflemlabelprefix{lem}
\frefformat{plain}{\fancyreflemlabelprefix}{{\freflemname}\fancyrefdefaultspacing#1}
\Frefformat{plain}{\fancyreflemlabelprefix}{{\Freflemname}\fancyrefdefaultspacing#1}

\newcommand{\case}[3][]{\mathsf{case}_{#1} #2 \mathsf{of} \{#3\}^m_{k=1}}
\newcommand{\data}{\mathsf{data} }
\newcommand{\where}{ \mathsf{where} }
\newcommand{\inl}{\mathsf{inl} }
\newcommand{\inr}{\mathsf{inr} }
\newcommand{\flet}[1][]{\mathsf{let}_{#1} }
\newcommand{\fin}{ \mathsf{in} }
\newcommand{\varid}[1]{\ensuremath{\Varid{#1}}}
\newcommand{\susp}[1]{⟦#1⟧}

\newcommand{\figuresection}[1]{\par \addvspace{1em} \textbf{\sf #1}}

\usepackage[colorinlistoftodos,prependcaption,textsize=tiny]{todonotes}
\setlength{\marginparwidth}{2.5cm} % Here's a size that matches the new PACMPL format -RRN
\usepackage{xargs}
\newcommandx{\unsure}[2][1=]{\todo[linecolor=red,backgroundcolor=red!25,bordercolor=red,#1]{#2}}
\newcommandx{\info}[2][1=]{\todo[linecolor=OliveGreen,backgroundcolor=OliveGreen!25,bordercolor=OliveGreen,#1]{#2}}
\newcommandx{\change}[2][1=]{\todo[linecolor=blue,backgroundcolor=blue!25,bordercolor=blue,#1]{#2}}
\newcommandx{\inconsistent}[2][1=]{\todo[linecolor=blue,backgroundcolor=blue!25,bordercolor=red,#1]{#2}}
\newcommandx{\critical}[2][1=]{\todo[linecolor=blue,backgroundcolor=blue!25,bordercolor=red,#1]{#2}}
\newcommandx{\improvement}[2][1=]{\todo[linecolor=Plum,backgroundcolor=Plum!25,bordercolor=Plum,#1]{#2}}
\newcommandx{\resolved}[2][1=]{\todo[linecolor=OliveGreen,backgroundcolor=OliveGreen!25,bordercolor=OliveGreen,#1]{#2}} % use this to mark a resolved question
\newcommandx{\thiswillnotshow}[2][1=]{\todo[disable,#1]{#2}} % will replace \resolved in the final document

% Peanut gallery comments by Ryan:
\newcommandx{\rn}[1]{\todo[]{RRN: #1}}
\newcommandx{\simon}[1]{\todo[]{SPJ: #1}}

% Link in bibliography interpreted as hyperlinks.
\newcommand{\HREF}[2]{\href{#1}{#2}}

% \newtheorem{definition}{Definition}
% \newtheorem{lemma}{Lemma}
\newtheorem{remark}{Remark}

\newcommand\calc{{\ensuremath{λ^q_\to}}}

\usepackage{booktabs} % For formal tables

% \usepackage[ruled]{algorithm2e} % For algorithms
% \renewcommand{\algorithmcfname}{ALGORITHM}
% \SetAlFnt{\small}
% \SetAlCapFnt{\small}
% \SetAlCapNameFnt{\small}
% \SetAlCapHSkip{0pt}
% \IncMargin{-\parindent}

% Metadata Information
\acmJournal{PACMPL}
\acmVolume{9}
\acmNumber{4}
\acmArticle{39}
\acmYear{2010}
\acmMonth{3}
\acmArticleSeq{11}

%\acmBadgeR[http://ctuning.org/ae/ppopp2016.html]{ae-logo}
%\acmBadgeL[http://ctuning.org/ae/ppopp2016.html]{ae-logo}


% Copyright
\setcopyright{acmcopyright}
%\setcopyright{acmlicensed}
%\setcopyright{rightsretained}
%\setcopyright{usgov}
% \setcopyright{usgovmixed}
%\setcopyright{cagov}
%\setcopyright{cagovmixed}

% DOI
\acmDOI{0000001.0000001}

% Paper history
\received{February 2017}
% \received{March 2009}
% \received[accepted]{June 2009}


% Document starts
\begin{document}
\DeclareUnicodeCharacter{8797}{\ensuremath{\stackrel{\scriptscriptstyle {\mathrm{def}}}{=}}}
\DeclareUnicodeCharacter{183}{\ensuremath{\cdot}} % ·

\newcommand\HaskeLL{Hask-LL}

% For outlining / psuedotext.
\newcommand{\note}[1]{
  \textcolor{blue}{
  \begin{itemize}
  \item #1
  \end{itemize}}}

\newcommand{\Red}[1]{\textcolor{red}{#1}}
\newcommand{\new}[1]{\textcolor{blue}{#1}}

% Title portion

% Put working title proposals here:
% \title{\HaskeLL}
% \title{\HaskeLL: Linear types with backwards compatibility in an established language}
% \title{\HaskeLL: Linear types with Backwards Compatibility}
% \title{\HaskeLL: Systems Programming with \\ Backwards-Compatible Linear Types}

% RRN: I don't think it's safe to highlight ``Systems Programming'' since we
% don't actually get to the point of demonstrating it (e.g. a working system +
% real systems programming in Hask-LL.)
\title{\HaskeLL: Backwards-Compatible Linear Types}
\def\shorttitle{Backwards-Compatible Linear Types}


\author{Jean-Philippe Bernardy}
\affiliation{%
  \institution{Gothenburg University}
  \department{Department of Philosophy, Linguistics and Theory of Science}
  \streetaddress{Olof Wijksgatan 6}
  \city{Gothenburg}
  % \state{VA}
  \postcode{41255}
  \country{Sweden}}
\author{Mathieu Boespflug}
\affiliation{%
  \institution{Tweag I/O}
  \city{Paris}
  % \state{VA}
  \postcode{???}
  \country{France}
}
\author{Ryan R. Newton}
\affiliation{%
  \institution{Indiana University}
  \city{Bloomington}
  % \state{VA}
  % \postcode{???}
  \country{USA}
}
\author{Simon Peyton Jones}
\affiliation{
  \institution{Microsoft Research}
  \city{Cambridge}
  \country{UK}
}
\author{Arnaud Spiwack}
\affiliation{
  \institution{Tweag I/O}
}
\affiliation{
  \institution{\textsc{Irif}, Université Paris Diderot}
  \city{Paris}
  \country{France}
}

% The default list of authors is too long for headers
\renewcommand{\shortauthors}{J.-P. Bernardy, M. Boespflug, R. Newton,
  S. Peyton Jones, and A. Spiwack}


\begin{abstract}
  Linear and affine type systems have a long and storied history, but not a
  clear path forward to integrate with existing languages such as Haskell.
  In this paper, we introduce a linear type system designed to enable
  backwards-compatibility and code reuse across linear and non-linear clients of
  a library.  Rather than bifurcate data types into linear and non-linear
  counterparts, we instead attach linearity to {\em binders}.  Linear function
  types can receive inputs from linearly-bound values, but can also operate over
  unrestricted, regular values.

  We formalise the proposed type-system in a core calculus; we provide a dynamic
  semantics as well as a proof of type safety.  Further, we show that every
  linear value is eventually deallocated, and not referenced thereafter.  We
  explore the applicability of linear typing in Haskell with a case study of a
  large, in-memory data structures that must serve responses with low latency.
\end{abstract}

%
% The code below should be generated by the tool at
% http://dl.acm.org/ccs.cfm
% Please copy and paste the code instead of the example below. 
%
\begin{CCSXML}
<ccs2012>
<concept>
<concept_id>10011007.10011006.10011008.10011024</concept_id>
<concept_desc>Software and its engineering~Language features</concept_desc>
<concept_significance>500</concept_significance>
</concept>
<concept>
<concept_id>10011007.10011006.10011008.10011009.10011012</concept_id>
<concept_desc>Software and its engineering~Functional languages</concept_desc>
<concept_significance>300</concept_significance>
</concept>
<concept>
<concept_id>10011007.10011006.10011039</concept_id>
<concept_desc>Software and its engineering~Formal language definitions</concept_desc>
<concept_significance>300</concept_significance>
</concept>
</ccs2012>
\end{CCSXML}

\ccsdesc[500]{Software and its engineering~Language features}
\ccsdesc[300]{Software and its engineering~Functional languages}
\ccsdesc[300]{Software and its engineering~Formal language definitions}
%
% End generated code
%

\keywords{Haskell, laziness, linear logic, Linear types, systems
  programming}

\thanks{This work has received funding from the European Commission
  through the SAGE project (grant agreement no. 671500).}

\maketitle


\section{Introduction}

Can we use Haskell to implement a low-latency server that caches
a large dataset in-memory? Today, the answer is
a clear\improvement{adapt to fit the ``running example''?}
``no''\footnote{https://blog.pusher.com/latency-working-set-ghc-gc-pick-two/},
because pauses incurred by garbage collection (GC), observed in the
order of 50ms or more, are unacceptable. Pauses are in general
proportional to the size of the heap. Even if the GC is incremental,
the pauses are unpredicable, difficult to control by the programmer
and induce furthermore for this particular use case a tax on overall
throughput. Typically, programmers therefore allocate these large,
long-lived data structures in manually-managed off-heap memory,
accessing it through FFI calls. Unfortunately this common technique
poses safety risks: not enforcing prompt deallocation, space leaks (by
failure to deallocate at all), as well use-after-free or double-free
errors as when programming in plain C.
It would be much better to rule out such problems via a type system.

It is well known that type systems can be useful for controlling resource usage, not just
ensuring correctness. \critical{Fix references}  Affine types~\cite{finishme}, linear
types~\cite{finishme}, permission types \cite{finishme}, and fractional
permissions \cite{finishme} enable safe manual memory management as well as safe
handling of scarce resources such as sockets and file handles.  All these
approaches have been extensively studied, \emph{yet these ideas have had relatively little
effect on programming practice}.  Few practical, full-scale languages are
designed from the start with such features.  Rust is the major
exception~\cite{matsakis_rust_2014}, and in Rust we see one of the attendant
complications: adding advanced resource-tracking features puts a burden on
language learners, who pass through
an initiation period of ``fighting the borrow checker''
\improvement{citation needed}.

Could more languages be extended with linear or affine types?  Unfortunately, there has
not been a clear path to augment preexisting type systems without (1) breaking
existing code, and (2) forcing the feature on users who do not need it, as in the
case of Rust.
% 
Recent work~\cite{best-of-both-worlds} has come closer to unifying linear and
unrestricted code, avoiding the need to {\em duplicate} basic library functions
like compose ($\circ$) or append (|++|) by adding incompatible linear versions.
Yet this approach still divides all types into unrestricted and linear, and adds
(non-)linearity constraints to the types of standard
combinators, including type-class constraints and complications that newcomers cannot easily
ignore.

We propose a new design that leaves most \emph{types} unmodified, and
instead associates linearity with {\em binders}, such as ``$\flet x \!:_{1}\! T =
\dots$'', indicating that $x$ must be used exactly once in the body.
%
We say that |x| is bound to a {\em linear value}, but |x| does not have a linear
{\em type}.
%
Only function types change to include (optional) linearity constraints on their
arguments.  However, these new linear functions are \emph{backward-compatible}:
they can be applied to non-linear values as well as linear ones.

We call the extended type system \HaskeLL{} --- Haskell meets Linear Logic.
With it we can enrich the types of standard Haskell Prelude functions, such as |map| and |++|,
by adding (but not requiring) the possibility of linear uses of those functions.
Existing function applications, such as |xs ++ ys|, continue to typecheck as
before, {\em unless} the inputs happen to be linear values.
% 
With this approach, a programmer does not need to worry about linearity
to use linear functions, and in fact may not even have to
{\em see} linearity information
unless the appropriate language extension is enabled.
We make the following contributions:

\begin{itemize}
\item We present a design for \HaskeLL{}, which offers linear typing in Haskell
  in a fully backward-compatible way (\fref{sec:programming-intro}). In particular, existing
  Haskell data types can contain linear values as well as non-linear ones;
  and linear functions can be applied to non-linear values.
  Most previous designs force an inconveniently
  sharp distinction between linear and non-linear code (\fref{sec:related}).
  Interestingly, our design is fully compatible with laziness, which has
  typically been challenging for linear systems because of the unpredictable
  evaluation order of laziness
  \cite[p9]{wakeling_linearity_1991}.\unsure{Though, to be honest, we
    don't run into problems because we don't have a lazy
    pattern-matching on linear data. Though I [aspiwack] don't think
    it's a useful feature for linear data: W\&R want to use it to make
    an infinite stream, but the stream must be consumed in its
    entirety so the program would just loop if it had some infinite
    linear data.}

\item We formalise \HaskeLL{} as \calc{}, a linearly-typed extension of the
  $λ$-calculus with data types (\fref{sec:statics}). We provide its type system,
  highlighting how it is compatible with existing Haskell features,
  including some popular extensions (the kind system, constraints, GADTs, and even dependent types).
  A distinctive feature of \calc{} is that linearity appears only in bindings
  and function arrows, rather than pervasively in all types.  Also unusually, we can readily
  support linearity polymorphism (\fref{sec:lin-poly}).

\item We provide a dynamic semantics for \calc{},
  combining laziness with explicit deallocation of linear data (\fref{sec:dynamics}).
  We prove type safety, of course.  But we also prove that the type system guarantees
  the key memory-management properties that we seek: that every
  linear value is eventually deallocated, and is never referenced after
  it is deallocated.

\end{itemize}
Our work is directly motivated by the needs of large-scale low-latency applications in industrial
practice. In \fref{sec:applications} we show how \HaskeLL{} meets those needs.
The literature is dense with related work, which we dicuss in \fref{sec:related}.


\section{A taste of \HaskeLL}
\label{sec:programming-intro}
We begin with an overview of
\HaskeLL, our proposed extension of Haskell with linear types.
%
First, along with the usual arrow type |A -> B|,
we propose an additional arrow type, standing for \emph{linear arrows}, written
|A ⊸ B|. In the body of a linear function, the type system tracks that
there is exactly one copy of the parameter to consume.

\begin{code}
f :: A ⊸ B
f x = {- |x| has multiplicity $1$ here -}
\end{code}
\noindent
We say that the \emph{multiplicity} of |x| is $1$ in the body of |f|. Similarly, we say
that unrestricted (non-linear) parameters have multiplicity $ω$ (usable
any number of times, including zero). We call
a function \emph{linear} if it has type |A ⊸ B| and \emph{unrestricted} if it has
type |A -> B|.

The linear arrow type |A ⊸ B| guarantees that any function with that type will
consume its argument exactly once.
However, a function of type |A ⊸ B|
\emph{places no requirement on the caller};
the latter is free to pass either a linear or non-linear value to the function.

For example, consider these definitions of a function |g|:
\begin{code}
g1,g2,g3 :: (Int ⊸ Int -> r) -> Int ⊸ Int -> r

g1 k x y = k x y          -- Valid
g2 k x y = k y x          -- Invalid: fails x's multiplicity guarantee
g3 k x y = k x (k y y)    -- Valid: y can be passed to linear k
\end{code}
As in |g2|, a linear variable |x| cannot be passed to the non-linear
function |(k y)|.  But the other way round is fine:
|g3| illustrates that the non-linear variable |y| can be passed
to the linear function |k|.

\subsection{Calling contexts and promotion}
\label{sec:calling-contexts}

The call of a linear function consumes its argument once only if the
call itself is consumed once.  For example, consider these definitions
of the same function |g|:
\begin{code}
f :: a ⊸ a
g4,g5,g6 :: (Int ⊸ Int -> r) -> Int ⊸ Int -> r

g4 k x y = k x (f y)      -- Valid: y can be passed to linear f
g5 k x y = k (f x) y      -- Valid: k consumes (f x)'s result once
g6 k x y = k y (f x)      -- Invalid: fails x's multiplicity guarantee
\end{code}
In |g5|, the linear |x| can be passed to |f| because the result of |(f x)| is
consumed linearly by |k|.  In |g6|, |x| is still passed to the linear function
|f|, but the call |(f x)| is in a non-linear context, so |x| too is
used non-linearly and the code is ill-typed.

\subsection{Linear data types}
\label{sec:linear-constructors}

Using the new linear arrow, we can (re-)define Haskell's list type as follows:
\begin{code}
data [a] where
  []   :: a
  (:)  :: a ⊸ [a] ⊸ [a]
\end{code}
That is, we give a linear type to the |(:)| data constructor.  This is
not a new, linear list type: this \emph{is} \HaskeLL{}'s list type, and all
Haskell functions will work over it perfectly well.  But we can
\emph{also} use the very same list type to contain linear resources (such as
file handles) without compromising safety; the type system will ensure
that resources in |xs| will eventually be deallocated, and that they
will not be used after that.

Many list-based functions conserve the multiplicity of data, and thus can
be given a more precise type. For example we can write |(++)| as follows:
\begin{code}
(++) :: [a] ⊸ [a] ⊸ [a]
[]      ++ ys = ys
(x:xs)  ++ ys = x : (xs ++ ys)
\end{code}
The type of |(++)| tells us that if we have a list |xs| with multiplicity $1$,
appending any other list to it will never duplicate any of the elements in |xs|,
nor drop any element in |xs|\footnote{This follows from parametricity.
  In order to {\em free} linear list elements, we must pattern match on them to
  consume them, and thus must know their type (or have a type class instance).
  Likewise to copy them.}.

But notice that giving a more precise type to |(++)| only
{\em strengthens} the contract that |(++)| offers to its callers;
\emph{but it does not restrict its usage}. For example:
\begin{code}
  sum :: [Int] ⊸ Int
  f :: [Int] ⊸ [Int] -> Int
  f xs ys = sum (xs ++ ys) + sum ys
\end{code}  
Here the two arguments to |(++)| have different multiplicities, but
the function |f| guarantees to consume |xs| precisely once.

For an existing language, being able to strengthen |(++)|, and similar functions, in a {\em
  backwards-compatible} way is a huge boon.
%
Of course, not all functions are linear: a function may legitimately
demand unrestricted input.
For example, the function |f| above consumed |ys| twice, and so |ys| must
have multiplicity $\omega$, and |f| needs an unrestricted arrow for that argument.

Generalising from lists to arbitrary algebraic data types,
we designed \HaskeLL{} so that linear constructors
correspond to regular Haskell data types when restricted to the
traditional (non-linear) Haskell fragment. Thus our radical position
is that data types in \HaskeLL{} should have {\em linear fields by default},
including all standard definitions, such as pairs, tuples, |Maybe|, lists, and so on.
More precisely, when defined in old-style Haskell-98 syntax, all fields are
linear; when defined using GADT syntax, the programmer can explicitly choose.
For example, in our system pairs defined as
\begin{code}
data (,) a b = (,) a b
\end{code}
would use linear arrows. This becomes explicit when defined in GADT syntax:
\begin{code}
data (a,b) where
  (,) ::  a ⊸ b ⊸ (a,b)
\end{code}
We will see in \fref{sec:non-linear-constructors} when it is useful
to have contstructors with unrestricted arrows.

\subsection{Linearity polymorphism} \label{sec:lin-poly}

Higher-order code is more complex, so we
introduce {\em multiplicity polymorphism} as a way to preserve
effective code sharing of higher-order functions. For example, the
standard |map| function over (linear) lists:

As seen above, implicit conversions between multiplicities make
first-order linear functions {\em more general}. But the higher-order
case thickens the plot. Consider that the standard |map| function over
(linear) lists,
\begin{code}
map f []      = []
map f (x:xs)  = f x : map f xs
\end{code}
can be given the two following incomparable types:
  |(a ⊸ b) -> [a] ⊸ [b]|  and
  |(a -> b) -> [a] -> [b]|.
%
In \HaskeLL{}, we can generalise over linear and unrestricted arrows
using {\em multiplicity polymorphism}. This is written $A →_ρ B$. In
the case at hand, |map| can be given the following most general type:
| ∀ρ. (a -> _ ρ b) -> [a] -> _ ρ [b]|
%
Likewise, function composition can be given the following general type:
\begin{code}
(∘) :: forall π ρ. (b → _ π c) ⊸ (a → _ ρ b) → _ π a → _ (ρ π) c
(f ∘ g) x = f (g x)
\end{code}
That is: two functions that accept arguments of arbitrary
multiplicities ($ρ$ and $π$ respectively) can be composed to form a
function accepting arguments of multiplicity $ρπ$ (\emph{i.e.} the
product of $ρ$ and $π$ --- see \fref{def:equiv-mutiplicity}).
%
Finally, from a backwards-compatibility perspective, all of these
subscripts and binders for multiplicity polymorphism can be {\em
  ignored}. Indeed, in a context where client code does not use
linearity, all inputs will have multiplicity $ω$, and transitively all
expressions can be promoted to $ω$. Thus in such a context the
compiler, or indeed documentation tools, can even altogether hide
linearity extensions from the programmer.

\subsection{Operational intuitions}
\label{sec:invariant} \label{sec:consumed}

Suppose that a linear function takes as its argument a {\em resource},
such as a file handle, channel, or memory block.  Then the function guarantees:
\begin{itemize}
\item that the resource will be consumed and destroyed by the time it returns;
\item that the resource can only be consumed once so will never be
  used after being destroyed.
\end{itemize}
In this way, the linear type system of \HaskeLL{} ensures both that
resource deallocation happens, and that no use-after-free error
occurs.

But wait! We said earlier that a non-linear value can be passed to a linear
function, so it would absolutely \emph{not} be safe for the function to deallocate the
value when it consumes it!  To understand this we need to explain our operational model.

In our model there there are two heaps: the familiar
\emph{dynamic heap} managed by the garbage collector, and a \emph{linear heap}
managed by the programmer supported by statically-checked guarantees.
We assume two primitives to allocate and free objects on the linear heap:
\begin{code}
allocT  :: (T ⊸ IO a) ⊸ IO a
freeT   :: T ⊸ ()
\end{code}
Here |allocT k| allocates a value of type |T| on the linear heap, and passes it to |k|.
The continuation |k| must eventually free |T| by calling |freeT|.
If there are any \emph{other} ways of
making a value of type |T| on the dynamic heap (e.g. |mkT :: Int -> T|),
then |freeT| might be given either a value on the linear heap or the dynamic heap.
It can only free the former, so it must make a dynamic test to tell which is the case.

A consequence of the above design is that unrestricted values never
contain (point to) linear values. (But the converse is possible.)
One can make sense of this rule operationally  by appealing to
garbage collection: when an unrestricted object is reclaimed by GC,
it would leave all resources that it points to unaccounted
for. Conversely, a pointer from a resource to the heap can simply act
as a new GC root.  We prove this invariant in \fref{sec:dynamics}.

We have repeatedly said that a linear function guarantees to ``consume'' its
argument exactly once if the call is consumed exactly once.
What precisely does ``consume'' mean?  We can now give a more precise operational
intution:
\begin{itemize}
\item To consume an atomic base type once, like |Int| or |Ptr|, just evaluate it.
\item To consume a function value once, call it once, and consume its result once.
\item To consume a pair once, evaluate it and consume each of its components once.
\item More generally, to consume a value of an algebraic data type once, evaluate
  it and consume all its linear components once.
\end{itemize}

In general, any sub-expression is type-checked as if it were to be
consumed exactly once. However, an expression which does not contain
resources, that is an expression whose free variables all have
multiplicity $ω$, can be consumed many times. Such an
expression is said to be \emph{promoted}. We leave the specifics to
\fref{sec:statics}.

\subsection{Linearity of constructors: the usefulness of unrestricted constructors}
\label{sec:non-linear-constructors}

We saw in \fref{sec:linear-constructors} that data types in \HaskeLL{} have
linear arguments by default. Do we ever need data constructors
unrestricted arguments?  Yes, we do.

Using the type |T| of \fref{sec:consumed}, suppose we wanted a primitive
to copy a |T| from the linear heap to the dynamic heap. We could define it
in CPS style like this
\begin{code}
  copyT :: (T -> r) ⊸ T ⊸ r
\end{code}
But a direct-style interface is more convenient:
\begin{code}
  copyT :: T ⊸ Unrestricted a
\end{code}
where |Unrestricted| is a data type with
a non-linear constructor\footnote{The type constructor
  |Unrestricted| is in fact an encoding of the so-called \emph{exponential}
  modality written ${!}$ in linear logic.}:
\begin{code}
  newtype Unrestricted a where
    Unrestricted :: a → Unrestricted a
\end{code}
The |Unrestricted|
data type is used to indicate that when a value |(Unrestricted x)| is consumed
once (see \fref{sec:consumed}) we have no guarantee about how often |x| is
consumed.
With our primitive in hand, we can now use ordinary code to copy
a linear list of |T| values into the dynamic heap:
\begin{code}
  copy :: (a ⊸ Unrestricted a) -> [a] ⊸ Unrestricted [a]
  copy copyElt (x:xs) = Unrestricted (x':xs')  where  Unrestricted xs'  = copy xs
                                                      Unrestricted x'   = copyElt x
\end{code}
% We stress that the above does not reduce to the linear identity
% function, |id :: [a] ⊸ [a]|. Indeed, with the |copy| function
% we can write the following linear
% function, which passes a linear list by copy to the unrestricted
% function |cycle| (if one were to replace |copy cpElem| by |id|, linearity would be violated).
% \begin{code}
%   f :: (a⊸Unrestricted a) -> [a] ⊸ [a]
%   f cpElem xs = cycle ys where Unrestricted ys = copy cpElem xs
% \end{code}


\subsection{Running example: zero-copy packets}
\label{sec:packet}

Crucially, our proposal has allowed the authors to solve latency
issues and improve throughput in a real-world application. Imagine
that you are writing a server application. It receives data, then
stores it for a while before sending it out to receivers, perhaps in
a different order. This general pattern characterizes a large class of
low-latency servers of in-memory data, such as
Memcached~\cite{memcached} or burst
buffers~\cite{liu_burstbuffer_2012}.

As an example, consider a software-defined packet switch. First, we
need to read packets from, and send them to, network interfaces.
Linearity can help with {\em copy-free} hand-off of packets between
network interfaces and in-memory data structures.
%
Assume that the user can acquire a linear handle on a {\em
  mailbox} of packets:

\begin{code}
  data MB
  withMailbox  :: (MB ⊸ IO a) ⊸ IO a
  close        :: MB ⊸ ()
\end{code}
The mailbox handle must be passed to |close| eventually in order to
release it.
%
|close| could be in the |IO| monad, but need not be --- linearity ensures
proper sequencing within the computation.  This is because |close|'s result must be
consumed with |case|, i.e. |case close mb of () -> e1| before we can |return| any result.
Receiving and
sending packets can likewise live outside of |IO|, and are ultimately part of the
|IO| action created with |withMailbox|:\improvement{[aspiwack] Simon
  convinced me that this was not actually the case if we consider that
  |get| and |send| have an effect on the rest of the |IO| action so
  they must not only be ordered between them, but also with respect to
  the |IO| action (separation logic analogy: mailboxes are not
  isolated regions) so |get| and |send| should be in |IO|, possibly
  |close| too (if it causes packets to bounce back for another
  process). None of this matters in the semantics of
  \fref{sec:dynamics}, so we may decide either to say: ``they should,
  in actuality, be in |IO| but for the sake of simplicity we forget
  about that'' or put these actions in |IO|. The latter's better, but
  then the semantics will be all annoying for little gain. }
\begin{code}
  get   :: MB ⊸ (Packet , MB)
  send  :: Packet ⊸ ()
\end{code}

|get| yields the next available packet, whereas |send| forwards it on the
network.
%
In the simplest case, we can read a message and send it immediately --- without
any filtering or buffering.
When calling |get| and |send|, |Packet|s never need to be copied:
they can be passed along from the network interface card to the mailbox
and then to the linear calling context of |send|, all by reference.

\paragraph{Buffering data in memory}

So what can our server do with the packets once they are retrieved
from the network? To support software defined switch policies that
dictate what packet to forward when, we introduce a priority queue.
\begin{code}
data PQ a
empty   :: PQ a
insert  :: Int -> a ⊸ PQ a ⊸ PQ a
next    :: PQ a ⊸ Maybe (a, PQ a)
\end{code}
The interface is familiar, except that since the priority queue must
accept packets it must have linear arrows. In this way, the type
system will \emph{guarantee} that despite being stored in a data
structure, every packet will eventually be sent.

In a packet switch, priorities could represent deadlines associated to
each packet\footnote{whereas in a caching application, the server may
  be trying to evict the bigger packets first in order to leave more
  room for incoming packets}. So we give ourselves a function to infer
a priority for a packet:
\begin{code}
  priority :: Packet ⊸ (Unrestricted Int,Packet)
\end{code}

The takeaway is that the priority queue can be implemented as
a \HaskeLL{} data type. Here is a naive implementation as a sorted
list:
\begin{code}
  data PQ a where
    Empty :: PQ a
    Cons :: Int -> a ⊸ PQ a ⊸ PQ a

  empty = Empty

  insert p x q Empty = Cons p x q
  insert p x (Cons p' x' q')  | p < p' = Cons p x (Cons p' x' q')
                              | otherwise = Cons p' x' (insert p x q')

  next Empty = Nothing
  next (Cons __ x q) = Just (x,q)
\end{code}
%
In \fref{sec:lower-gc}, we will return to the implementation of the
priority queue and discuss the implications for garbage collection
overheads.

Finally, here is a tiny packet switch that forwards all packets
on the network once three packets are available.
\begin{code}
  sendAll :: PQ Packet ⊸ ()
  sendAll q | Just (p,q')  <- next q = case send p of () -> sendAll q'
  sendAll q | Nothing      <- next q = ()

  enqueue :: MB ⊸ PQ a ⊸ (PQ a,MB)
  enqueue mb q =
    let
      !(p,mb')              = get mb
      !(!(Unrestricted prio),p')  = priority p
    in ( mb' , insert prio p' q )

  main :: IO ()
  main = withMailbox $ \ mb0 ->
    let
      !(mb1,q1)  = enqueue mb0 empty
      !(mb2,q2)  = enqueue mb1 q1
      !(mb3,q3)  = enqueue mb2 q2
      !()        = close mb3
    in return $ sendAll q3
\end{code}

\section{\calc{} statics}
\label{sec:statics}
In this section we turn to the calculus at the core of \HaskeLL{}, namely
\calc{}, for which we provide a step-by-step account of its syntax and typing
rules.

In \calc{}, there are two classes of values: \emph{linear values},
which must be used \emph{exactly once} on each code path, and
\emph{unrestricted values}, which can be used an arbitrary number of
times (including zero).

The best way to think of linear values is to see them as objects
that need not be controlled by the garbage collector: \emph{e.g.}
because they are scarce resources, because they are controlled by
foreign code.
The word \emph{need} matters here:
because of polymorphism, it is possible for any given linear value to
actually be controlled by the garbage collector, however, for most
purposes, it must be treated as if it it were not.
\improvement{MB: This paragraph is too imprecise as it stands.
  I reread it several times but am non the wiser for it, meaning it
  might as well be removed. Needs a rewrite.}

This framing drives the details of \calc{}. In particular, unrestricted
values cannot contain linear values
because the garbage collector needs to
control transitively the deallocation of every sub-object: otherwise we may
have dangling pointers or memory leaks. On the other hand, it is
valid for linear values to refer to unrestricted ones: linear values act as GC roots.
So any
value containing a linear value must also be linear. Crucially this property
applies to closures as well (both partial applications and lazy
thunks): \emph{e.g.} a partial application of a function to a linear
value is, itself, a linear value (which means that such
a partial application must be applied exactly once).
More generally, the application of a function
to a linear value is linear, since it is, in general, a closure
pointing to that linear value.

\subsection{Typing}
\label{sec:typing}

The term syntax (\fref{fig:syntax}) is that of a type-annotated
(\textit{à la} Church) simply typed $λ$-calculus with let-definitions.
Binders in $λ$-abstractions and type definitions are annotated both
with their type and their multiplicity (echoing the typing context
from \fref{sec:typing-contexts}). Multiplicity abstraction and
application are explicit.

In our static semantics for \calc{} the familiar judgement \(Γ ⊢ t :
A\) has a non-standard reading: it asserts that the term $t$ builds \emph{exactly one} $A$, and consumes all
of $Γ$.  This section precisely defines the syntax of types and the typing judgement.

\begin{figure}
  \figuresection{Multiplicities}
  \begin{align*}
    p,q &::= 1 ~||~ ω ~||~ π ~||~ p+q ~||~ p·q
  \end{align*}
  \figuresection{Contexts}
  \begin{align*}
    Γ,Δ & ::=\\
        & ||  x :_q A, Γ & \text{multiplicity-annotated binder} \\
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
      & ||  ∀ρ. A &\text{multiplicity-dependent type}\\
      & ||  D &\text{data type}
  \end{align*}

  \figuresection{Terms}
  \begin{align*}
    e,s,t,u & ::= \\
            & ||  x & \text{variable} \\
            & ||  λ(x:_qA). t & \text{abstraction} \\
            & ||  t_q s & \text{application} \\
            & ||  λπ. t & \text{multiplicity abstraction} \\
            & ||  t p & \text{multiplicity application} \\
            & ||  c t₁ … t_n & \text{data construction} \\
            & ||  \case[p] t {c_k  x₁ … x_{n_k} → u_k}  & \text{case} \\
            & ||  \flet x_1 :_{q₁}A₁ = t₁ … x_n :_{q_n}A_n = t_n \fin u & \text{let}
  \end{align*}

  \caption{Syntax of the linear calculus}
  \label{fig:syntax}
  \label{fig:contexts}
\end{figure}

The types of \calc{} (see \fref{fig:syntax}) are simple types with
arrows (albeit multiplicity-annotated ones), data types, and
multiplicity polymorphism. The annotated function type is a
generalization of the intuitionistic arrow and the linear arrow. We
use the following notations:
\begin{itemize}
\item \(A → B ≝  A →_ω B\)
\item \(A ⊸ B ≝ A →_1 B\)
\end{itemize}
The intuition behind the multiplicity-annotated arrow \(A →_q B\) is that you can
get a \(B\) if you can provide an \(A\) with multiplicity \(q\). Note in
particular that when one has $x :_ω A$ and $f :_1 A ⊸ B$, the call
$f x$ is well-typed. Therefore, the constraints imposed by multiplicities on
arrow types are dual to those they impose on variables in the context:
a function of type $A→B$ \emph{must} be applied to an argument of
multiplicity $ω$, while a function of type $A⊸B$ \emph{may} be applied to an
argument of multiplicity $1$ or $ω$.

One might expect the type $A⊸B$ to be a subtype of $A→B$. This is
however, not so: there is no notion of
subtyping in \calc{}. This is a salient choice in our design. Our objective is to integrate with
existing typed functional languages such as Haskell and the ML family, which are based on Hindley-Milner-style
polymorphism, where subtyping and polymorphism do not mesh well.
\improvement{Cite specific issues here (absence of principal types?).}
\calc{} uses polymorphism where other systems use subtyping.
\improvement{Can we cite prior art that falls in this category?}

Data type declarations (see \fref{fig:syntax}) are of the following form:
\begin{align*}
  \data D  \mathsf{where} \left(c_k : A₁ →_{q₁} ⋯    A_{n_k} →_{q_{n_k}} D\right)^m_{k=1}
\end{align*}
The above declaration means that \(D\) has \(m\) constructors
\(c_k\) (where \(k ∈ 1…m\)), each with \(n_k\) arguments. Arguments of
constructors have a multiplicity, just like arguments of functions:
an argument of multiplicity $ω$ means that the data type can store,
at that position, data which \emph{must} have multiplicity $ω$;
while a multiplicity of $1$ means that data at that position
\emph{can} have multiplicity $1$ (or $ω$). A further requirement is
that the multiplicities $q_i$ must be concrete (\emph{i.e.} either
$1$ or $ω$).

For most purposes, $c_k$ behaves like a constant with the type
$A₁ →_{q₁} ⋯ A_{n_k} →_{q_{n_k}} D$ \unsure{MB: Shouldn't these be lollipops?}. As the typing rules of
\fref{fig:typing} make clear, this means in particular that from a
value $d$ of type $D$ with multiplicity $ω$, pattern matching
extracts the elements of $d$ with multiplicity $ω$. Conversely, if all
the arguments of $c_k$ have multiplicity $ω$, $c_k$ constructs $D$
with multiplicity $ω$.

Note that, as discussed in \fref{sec:linear-constructors},
constructors with arguments of multiplicity $1$ are not more general
than constructors with arguments of multiplicity $ω$, because if, when
constructing $c u$, with the argument of $c$ of multiplicity $1$, $u$
\emph{may} be either of multiplicity $1$ or of multiplicity $ω$,
dually, when pattern-matching on $c x$, $x$ \emph{must} be of
multiplicity $1$ (if the argument of $c$ had been of multiplicity $ω$,
on the other hand, then $x$ could be used either as having
multiplicity $ω$ or $1$).

It is perhaps more surprising that applications and cases are
annotated by a multiplicity. This information is usually redundant,
but we use it in \fref{sec:dynamics} to define a compositional
dynamic semantics with prompt deallocation of data. We sometimes omit
the multiplicities or type annotations when they are obvious from the
context, especially in the case of applications.\unsure{[aspiwack]
  Though, to be honest, we also need the type of the argument now (for
  let-introduction), and we don't keep it. I'm tempted to drop these
  annoying annotations and define the translation in the dynamics
  section as acting on type derivations rather than terms which happen
  to be well-typed}

%%% typing rule macros %%%
\newcommand{\apprule}{\inferrule{Γ ⊢ t :  A →_q B  \\   Δ ⊢ u : A}{Γ+qΔ ⊢ t_q u  :  B}\text{app}}
\newcommand{\varrule}{\inferrule{ }{ωΓ + x :_1 A ⊢ x : A}\text{var}}
\newcommand{\caserule}{\inferrule{Γ   ⊢  t  : D  \\ Δ, x₁:_{pq_i} A_i, …,
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

    \inferrule{Δ_i ⊢ t_i : A_i \\ \text {$c_k : A_1 →_{q_1} … →_{q_{n-1}}
        A_n →_{q_n} D$ constructor}}
    {ωΓ+\sum_i q_iΔ_i ⊢ c_k  t₁ … t_n : D}\text{con}

    \caserule

    \inferrule{Γ_i   ⊢  t_i  : A_i  \\ Δ, x₁:_{q₁} A₁ …  x_n:_{q_{n}} A_n ⊢ u : C }
    { Δ+\sum_i q_iΓ_i ⊢ \flet x_1 :_{q₁}A_1 = t₁  …  x_n :_{q_n}A_n = t_n  \fin u : C}\text{let}

    \inferrule{Γ ⊢  t : A \\ \text {$π$ fresh for $Γ$}}
    {Γ ⊢ λπ. t : ∀π. A}\text{m.abs}

    \inferrule{Γ ⊢ t :  ∀π. A}
    {Γ ⊢ t p  :  A[p/π]}\text{m.app}
  \end{mathpar}

  \caption{Typing rules}
  \label{fig:typing}
\end{figure}

\subsection{Contexts}
\label{sec:typing-contexts}
Most typing rules mutiply contexts by a multiplicity. In this
subsection we explain what this means and in general discuss the
structure of contexts.

In \calc{}, each variable in typing contexts is annotated with a
multiplicity.
Concrete multiplicities are either $1$ or $ω$ which stand for linear
and unrestricted bindings, respectively. For the sake of
polymorphism, multiplicities are extended with multiplicity
\emph{expressions}, which contain variables (ranged over by the
metasyntactic variables \(π\) and \(ρ\)), sum\resolved{We use sums
  nowhere in the examples; shall we remove this? -- [Aspiwack] in the
  case of $1$/$ω$ multiplicity $π+ρ$ is always (implicitly) $ω$, so
  there may indeed be no benefit to formal sums in the scope of this
  paper. JP: in the end it is somewhat ugly to remove sums, and we get to the situation that we can no longer extend to $0$ multiplicities. So let's keep them.},
and product. The complete syntax of multiplicities and
contexts can be found in \fref{fig:contexts}.

In addition, multiplicities are equipped with an equivalence relation,
written $(=)$, and defined as follows:
\begin{definition}[equivalence of multiplicities]
  \label{def:equiv-mutiplicity}
  The equivalence of multiplicities is the smallest transitive and
  reflexive relation, which obeys the following laws:
\begin{itemize}
\item $+$ and $·$ are associative and commutative
\item $1$ is the unit of $·$
\item $·$ distributes over $+$
\item $ω · ω = ω$
\item $1 + ω = ω$
\item $1 + 1 = ω$
\item $ω + ω = ω$
\end{itemize}
\end{definition}
Thus, multiplicities form a semi-ring (without a zero), which extends to a
module structure on typing contexts as follows.

\begin{definition}[Context addition]~
  \begin{align*}
    (x :_p A,Γ) + (x :_q A,Δ) &= x :_{p+q} A, (Γ+Δ)\\
    (x :_p A,Γ) + Δ &= x :_p A, Γ+Δ & (x ∉ Δ)\\
    () + Δ &= Δ
  \end{align*}
\end{definition}
Context addition is total: if a variable occurs in both operands the
first rule applies (with possible re-ordering of bindings in $Δ$), if
not the second or third rule applies.

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

The equivalence relation is lifted to contexts in the obvious way. In
the typing rules contexts can always be substituted for other
equivalent contexts.

\subsection{Typing rules}
We are now ready to understand the typing rules of
\fref{fig:typing}. Remember that the typing judgement \(Γ ⊢ t : A\)
reads as: the term $t$ consumes $Γ$ and builds an $A$ with
multiplicity $1$.  This is the only kind of judgement in \calc{}:
there is no direct way to express ``the term $t$ consumes $Γ$ and
builds an $A$ with multiplicity $p$''. The reason for this is the
\emph{promotion principle}\footnote{The name \emph{promotion
    principle} is a reference to the promotion rule of linear
  logic. In \calc{}, however, promotion is implicit.}: to know how to
create an unrestricted value it is sufficient (and, in fact,
necessary) to know how to create a linear value. Thinking in terms of
resources is the easiest way to shed light on this principle: a value
which does not contain resources can safely be shared or dropped.

The promotion principle is formalised through the use of context
scaling in rules such as the application rule:
$$\apprule$$
The idea is that since $Δ ⊢ u : A$ means creating a $u$ with
multiplicity $1$, scaling the context to $qΔ$ also (implicitly) scales
the right-hand side of the judgement: that is it creates a $u$ with
multiplicity $q$ (as required by the function). To get a better grasp
of this rule, you may want to consider how it indeed renders the
following judgement well-typed. In this judgement, $π$ is a
multiplicity variable, that is the judgement is multiplicity-polymorphic:
$$f:_ωA→_πB, x:_π A ⊢ f x$$

This implicit use of the promotion principle in rules such as the
application rule is the technical device
which makes the intuitionistic $λ$-calculus a subset of
\calc{}. Specifically the subset where all variables are annotated
with the multiplicity $ω$:
$$
\inferrule
{\inferrule
  {\inferrule
    {\inferrule{ }{x :_ω A ⊢ x : A}\text{var} \qquad \inferrule{ }{x :_ω A ⊢ x : A}\text{var}}
    {x :_ω A ⊢ Tensor x x : Tensor A A}\text{con}}
  {⊢ λ (x :_ω A). Tensor x x : A →_ω Tensor A A}\text{abs} \qquad \inferrule{\vdots}{⊢ id_ω 42 : A}}
{()+ω() ⊢ (λ (x :_ω A). Tensor x x)_ω \; (id_ω \; 42)}\text{app}
$$
This latter fact is, in turn, why \HaskeLL{} is an extension of Haskell
(provided unannotated variables are understood
to have multiplicity $ω$).

The variable rule, used in the above example, may require some
clarification.
$$\varrule$$
The variable rule is the rule which implements weakening of
unrestricted variables: that is, it lets us ignore variables with
multiplicity $ω$\footnote{Pushing weakening to the variable rule is
  classic in many lambda calculi, and in the case of linear logic,
  dates back at least to Andreoli's work on
  focusing~\cite{andreoli_logic_1992}.}. Note that the judgement
$x :_ω A ⊢ x : A$ is an instance of the variable rule, because
$(x :_ω A)+(x :_1 A) = x:_ω A$. The constructor rule has a similar
$ωΓ$ context: it is necessary to support weakening at the level of
constant constructors.

Most of the other typing rules are straightforward, but let us linger
for a moment on the case rule:
$$\caserule$$
Like the application rule it is parametrized by a multiplicity
$p$\improvement{[aspiwack] If I remove annotation on applications this
will have to go}. But, while in the application rule only the argument is affected
by $p$, in the case rule, not only the scrutinee but also the variable
bindings in the branches are affected by $p$. What it means,
concretely, is that the multiplicity of data is \emph{inherited} by
its elements: if we have an $(A,B)$ with multiplicity $1$, then we have
an $A$ with multiplicity $1$ and a $B$ with multiplicity $1$, and if
we have an $(A,B)$ with multiplicity $ω$ then we have an $A$ with
multiplicity $ω$ and a of $B$ with multiplicity $ω$. Therefore, the
following program, which asserts the existence of projections, is
well-typed (note that, both in |first| and |snd|, the arrow is~---~and
must be~---~unrestricted).
\begin{code}
  first  ::  (a,b) →   a     bigSpace    snd  ::  (a,b) →   b
  first      (a,b)  =  a                 snd      (a,b)  =  b
\end{code}

The reason why this inheritance of multiplicity is valid stems from
our understanding of unrestricted values: an unrestricted value is
owned by the garbage collector, which must also own its elements
recursively. Phrased in terms of resources: if a value does not
contain linear resources, neither do its elements.

Inheritance of multiplicity is not necessary for the rest of the system
to work. Yet, it is a design choice which makes it possible to consider
data-type constructors as linear by default, while preserving the
semantics of the intuitionistic $λ$-calculus (as we already alluded to
in \fref{sec:linear-constructors}). For \HaskeLL{}, it means that types
defined in libraries which are not aware of linear type (\emph{i.e.}
libraries in pure Haskell) can nevertheless be immediately useful in a
linear context. Inheritance of multiplicity is thus crucial for
backwards compatibility, which is a design goal of \HaskeLL{}.

\section{\calc{} dynamics}
\label{sec:dynamics}

We wish to give a dynamic semantics for \calc{} which accounts for the
packet forwarding example of \fref{sec:packet} where packets are
kept out of the garbage collected heap, and freed immediately upon
send. To that effect we follow \citet{launchbury_natural_1993} who
defines a semantics for lazy computation. We will need also to account
for the |IO| monad, which occurs in the \textsc{api} for packets.

\subsection{The IO monad}

Linear typing allows to safely and easily express world-passing
semantics. \Citet{launchbury_st_1995} defines
|IO a| as |World -> (World , a)|, for an abstract type |World| representing the state of the
entire world. The idea is that every time some |IO| action is
undertaken, the world has possibly changed so we \emph{consume} the
current view of the world and return the new version.

The above gives a pure interface to \textsc{i/o}. However, it leaves the possibility
for the programmer to access and old version of the world, as well as the current
one, which is expensive to implement. In practice, one does not want to perform such a duplication,
and thus Haskell solves the issue by forcing the
programmer to use |IO| via its monadic interface.

Linear typing gives a much more direct solution to the problem: if the
|World| is kept linear, then there is no way to observe two different
|World|s. Namely, it is enough to define |IO| as
\improvement{Write definition of |IO| in \calc{} syntax}
\begin{code}
  data IO0  a where IO0 : World ⊸ a -> IO0 a
  type IO   a = World ⊸ IO0 a
\end{code}
Notice that the |a| of |IO a| is always unrestricted, so that |IO| has
the same semantics as in Haskell (it is also the semantics which we
need to ensure that |withMailbox| is safe).

The last missing piece is to inject a |World| to start the
computation. Haskell relies on a |main :: IO ()| function, of which
there must be a single one at link time. In \calc{} the simplest way
to achieve the same result is to start computation with a $world :_1
\varid{World}$ in the context.

In general, a top-level definition of multiplicity $1$ corresponds to
something which must be consumed exactly once at link time, which
generalises the concept of the |main| function (if only slightly).

\subsection{Modelling network traffic}
\label{sec:model-io}

We are not going to give an accurate, non-deterministic, model of
\textsc{i/o} for the purpose of this section. Instead, we are going to
consider the semantics as a Laplace demon: the entirety of the events
past and future are pre-ordained, and the semantics has access to this
knowledge.

Because the only interaction in the world which we need to model in
order to give a semantics to the packet example of \fref{sec:packet}
is to obtain a packet, it will be sufficient for this section to
consider all the packets. Because there are several mailboxes and each
can get their own streams of packets, we suppose implicitly a
given collection of packets $(p^j_i)_{j,i∈ℕ}$. Where the packet
$p^j_i$ represents the $i$-th package which will be received by the
$j$-th mailbox.

Instead of using the world token as a proxy for an abstract world, we
are going to use it to keep track of how many mailboxes have been
opened. So the (unique) world token in the stack will hold this number.
Similarly, the mailbox tokens will be pairs $⟨j,i⟩$ of
integers where $j$ is the mailbox number and $i$ the number of packets
the mailbox has received. In effect, the world and mailbox tokens are
pointers into the infinite matrix of potential packets. We will define
these constants as having the same typing rules as zero-ary constructors
(but without the pattern-matching rule):
\emph{e.g.}:
$$
\inferrule{ }{ωΓ ⊢ j : \varid{World}}\text{world}
$$

In addition to the abstract types $\varid{World}$, $Packet$ and $\varid{MB}$, and the
concrete types $IO_0$, $IO$, $(,)$, and $()$, \calc{} is extended with
three primitives (see also \fref{sec:packet}):
\begin{itemize}
\item |withMailbox :: (MB ⊸ IO a) ⊸ IO a|
\item |get :: MB ⊸ (Packet , MB)|
\item |send :: Packet ⊸ ()|
\end{itemize}
Packets $p^j_i$ are considered
constant.\improvement{reference to primitives which are dropped for
  the sake of simplicity}

\subsection{Operational semantics}

\citeauthor{launchbury_natural_1993}'s semantics is a big-step
semantics where variables play the role of pointers to the heap (hence
represent sharing, which is the cornerstone of a lazy semantics).

To account for a foreign heap, we have a single logical heap with
bindings of the form $x :_p A = e$ where $p∈\{1,ω\}$ a multiplicity:
bindings with multiplicity $ω$ represent objects on the regular,
garbage-collected, heap, while bindings with multiplicity $1$
represent objects on a foreign heap, which we call the \emph{linear
  heap}. The linear heap will hold the $\varid{World}$ and $\varid{MB}$ tokens as well
as packets. \citet{launchbury_natural_1993}'s semantics relies on a
constrained $λ$-calculus syntax which we remind in
\fref{fig:launchbury:syntax}. We assume, in addition, that the
primitives are $η$-expanded by the translation.

\improvement{in the translation, add rules for the multiplicity abstraction
  and application}

\begin{figure}
  \figuresection{Translation of typed terms}
  \begin{align*}
    (λ(x:_qA). t)^* &= λ(x:_qA). (t)^* \\
    x^*             &= x \\
    (t_q  x )^*     &= (t)^*_q  x \\
    (t_q  u )^*     &= \flet y :_q \_ = (u)^* \fin (t)^*  y \\
    c_k  t₁ … t_n   &= \flet x₁ :_{q_1} \_ = (t₁)^*,…, x_n :_{q_n} \_ = (t_n)^*
                      \fin c_k x₁ … x_n
  \end{align*}
  \begin{align*}
    (\case[p] t {c_k  x₁ … x_{n_k} → u_k})^* &= \case[p] {(t)^*} {c_k  x₁ … x_{n_k} → (u_k)^*} \\
    (\flet x_1:_{q₁}A_1= t₁  …  x_n :_{q_n}A_n = t_n \fin u)^* & = \flet x₁:_{q₁}A_1 = (t₁)^*,…, x_n :_{q_n}A_n=_{q_n} (t_n)^* \fin (u)^*
  \end{align*}

  \caption{Syntax for the Launchbury-style semantics}
  \label{fig:launchbury:syntax}
\end{figure}

\unsure{Should we use handles with a separate heap for Packets, with
  handle in the linear heap? It makes the semantics significantly more
  verbose, but at least you don't have packets jumping to and from the
  linear heap. — [aspiwack] I feel that adding heap and handles would
  make the proofs much more tedious}
The dynamic semantics is given in \fref{fig:dynamics}. Let us review
the new rules
\begin{description}
\item[Linear variable] In the linear variable rule, the binding in the
  linear heap is removed. In conjunction with the rule for $send$, it
  represents deallocation of packets.
\item[WithMailbox] A new $\varid{MB}$ is created with a fresh name ($j$). Because it
  has not received any message yet, the mailbox token is $⟨j,0⟩$, and the
  world token is incremented. The body $k$ is an $IO$ action, so it takes
  the incremented world as an argument and returns a new one, which is then
  returned as the final world after the entire $withMailbox$ action.
\item[Get] The $get$ primitive receives the next packet as is
  determined by the $(p^j_i)_{j,i∈ℕ}$ matrix, and the number of
  packets received by the $\varid{MB}$ is incremented.
\item[Send] The $send$ primitive does not actually change the world,
  because all the messages that will ever be received are preordained,
  by assumption. So, from the point of view of this semantics,
  $send$ simply frees its argument: the packet is stored in
  a linear variable, so it is removed from the heap with the linear
  variable rule; then the send rule drops it.
\end{description}

\subsection{Type safety}

\todo{move the statements of the theorem to the beginning of the
  section}

\begin{figure}
  \begin{mathpar}
    \inferrule{ }{Γ : λπ. t ⇓ Γ : λπ. t}\text{m.abs}


    \inferrule{Γ : e ⇓ Δ : λπ.e' \\ Δ : e'[q/π] ⇓ Θ : z} {Γ :
      e q ⇓ Θ : z} \text{m.app}

    \inferrule{ }{Γ : λx:_pA. e ⇓ Γ : λx:_pA. e}\text{abs}


    \inferrule{Γ : e ⇓ Δ : λy:_pA.e' \\ Δ : e'[x/y] ⇓ Θ : z} {Γ :
      e x ⇓ Θ : z} \text{application}

    \inferrule{Γ : e ⇓ Δ : z}{(Γ,x :_ω A = e) : x ⇓ (Δ;x :_ω A z) :
      z}\text{shared variable}


    \inferrule{Γ : e ⇓ Δ : z} {(Γ,x :_1 A = e) : x ⇓ Δ :
      z}\text{linear variable}


    \inferrule{(Γ,x_1 :_ω A_1 = e_1,…,x_n :_ω A_n e_n) : e ⇓ Δ : z}
    {Γ : \flet x₁ :_{q₁} A_1 = e₁ … x_n :_{q_n} A_n = e_n \fin e ⇓ Δ :
      z}\text{let}

    \inferrule{ }{Γ : c  x₁ … x_n ⇓ Γ : c  x₁ …
      x_n}\text{constructor}


    \inferrule{Γ: e ⇓ Δ : c_k  x₁ … x_n \\ Δ : e_k[x_i/y_i] ⇓ Θ : z}
    {Γ : \case[q] e {c_k  y₁ … y_n ↦ e_k } ⇓ Θ : z}\text{case}

    \inferrule{Γ, x:_1 \varid{MB} = ⟨j,0⟩ : k x (j+1) ⇓ Δ:z}{Γ,w:_1 \varid{World} = j:withMailbox k w ⇓ Δ:z}\text{withMailbox}

    \inferrule
      {Γ:x ⇓ Δ:⟨j,i⟩}
      {Γ:get x ⇓ Δ,x:_1 \varid{MB} = ⟨j,i+1⟩, y:_1 Packet = p^j_i : (y,z)}\text{get}

    \inferrule{Γ:x ⇓ Δ:p^j_i}{Γ:send x ⇓ Δ:()}\text{send}
  \end{mathpar}

  \caption{Dynamic semantics}
  \label{fig:dynamics}
\end{figure}
\todo{add `close : MB ⊸ ()` in the semantcs}

While the semantics of \fref{fig:dynamics} describes quite closely
what our plans for implementation in the \textsc{ghc}, it is not
convenient for proving properties. There are two reasons to that fact:
first the semantics follows a different structure than the type system and, also,
there are pointers from the garbage-collected heap to the linear
heap. Such pointers occur, for instance, in the priority queue from
\fref{sec:packet}: the queue itself is allocated on the garbage
collected heap while packets are kept in the linear heap.

This is not a problem in and on itself: pointers to packets may be seen
as opaque by the garbage collector which will not collect them, so
that their lifetime is still managed explicitly by the
programmer. However, in order to prevent use-after-free bugs, we must
be sure that by the time a packet is sent (hence freed), every extant object in the
garbage-collected heap which points to that packet must be dead.

In order to prove such a property, let us introduce a stronger
semantics with the lifetime of objects more closely tracked. The
strengthened semantics differs from \fref{fig:dynamics} in two
aspects: the evaluation states are typed, and values with statically
tracked lifetimes (linear values) are put on the linear
heap.
%
In order to define the typed semantics, we introduce a few
notations. First we need a notion of product annotated with the
multiplicity of its first component.
\begin{definition}[Weighted tensors]

  We use $A~{}_ρ\!⊗ B$ ($ρ∈\{1,ω\}$) to denote one of the two following
  types:
  \begin{itemize}
  \item $\data A~{}_1\!⊗ B = ({}_1\!,) : A ⊸ B ⊸ A~{}_1\!⊗ B$
  \item $\data A~{}_ω\!⊗ B = ({}_ω\!,) : A → B ⊸ A~{}_ω\!⊗ B$
  \end{itemize}

\end{definition}
Weighted tensors are used to internalise a notion of stack that keeps
track of multiplicities for the sake of the following definition, which
introduces the states of the strengthened evaluation relation.

\newcommand{\termsOf}[1]{\mathnormal{terms}(#1)}
\newcommand{\multiplicatedTypes}[1]{\mathnormal{multiplicatedTypes}(#1)}

\begin{definition}[Annotated state]


  An annotated state is a tuple $Ξ ⊢ (Γ||t :_ρ A),Σ$ where
  \begin{itemize}
  \item $Ξ$ is a typing context
  \item $Γ$ is a \emph{typed heap}, \emph{i.e.} a collection of
    bindings of the form $x :_ρ A = e$
  \item $t$ is a term
  \item $ρ∈\{1,ω\}$ is a multiplicity
  \item $A$ is a type
  \item $Σ$ is a typed stack, \emph{i.e.} a list of triple $e:_ω A$ of
    a term, a multiplicity and an annotation.
  \end{itemize}
\end{definition}
\begin{definition}[Well-typed state]
  We say that an annotated state is well-typed if the following
  typing judgement holds:
  $$
  Ξ ⊢ \flet Γ \fin (t,\termsOf{Σ}) : (A~{}_ρ\!⊗\multiplicatedTypes{Σ})‌
  $$
  Where $\flet Γ \fin e$ stands for the grafting of $Γ$ as a block of
  bindings, $\termsOf{e_1 :_{ρ_1} A_1, … , e_n :_{ρ_n} A_n}$
  for $(e_1~{}_{ρ_1}\!, (…, (e_n~{}_{ρ_n},())))$, and
  $\multiplicatedTypes{e_1 :_{ρ_1} A_1, … , e_n :_{ρ_n} A_n}$ for
  $A_1~{}_{ρ_1}\!⊗(…(A_n~{}_{ρ_n}\!⊗()))$.
\end{definition}

\begin{definition}[Strengthened reduction relation]
  We define the strengthened reduction relation, also written $⇓$, as a
  relation on annotated states. Because $Ξ$, $ρ$, $A$ and $Σ$ are
  always the same for related states, we abbreviate
  $$
  (Ξ ⊢ Γ||t :_ρ A,Σ) ⇓ (Ξ ⊢ Δ||z :_ρ A,Σ)
  $$
  as
  $$
  Ξ ⊢ (Γ||t ⇓ Δ||z) :_ρ A, Σ
  $$

  The strengthened reduction relation is defined inductively by the
  rules of \fref{fig:typed-semop}.
\end{definition}
\begin{figure}
  \begin{mathpar}
\inferrule{ }{Ξ ⊢ (Γ || λx:_qA. e ⇓ Γ || λx:_qA. e) :_ρ A→_q B}\text{abs}

\inferrule
    {Ξ  ⊢  (Γ||e      ⇓ Δ||λ(y:_q A).u):_ρ A →_q B, x:_{qρ} A, Σ \\
     Ξ  ⊢  (Δ||u[x/y] ⇓ Θ||z)   :_ρ       B,            Σ}
    {Ξ  ⊢  (Γ||e_q x ⇓ Θ||z) :_ρ B ,Σ}
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
  {Ξ ⊢ (Γ,       x_1 :_{ρq_1} A_1 = e_1 … x_n :_{pq_n} A_n = e_n  ||  t ⇓ Δ||z) :_ρ C, Σ}
  {Ξ ⊢ (Γ||\flet x_1 :_{q_1}  A_1 = e_1 … x_n :_{q_n} A_n = e_n \fin t ⇓ Δ||z) :_ρ C, Σ}
{\text{let}}

\inferrule
  { }
  {Ξ ⊢ (Γ || c x_1…x_n  ⇓ Γ || c x_1…x_n) :_ρ A, Σ}
{\text{constructor}}

\inferrule
  {Ξ,y_1:_{p_1qρ} A_1 … ,y_n:_{p_nqρ} A_n ⊢ (Γ||e ⇓ Δ||c_k x_1…x_n) :_{qρ} D, u_k:_ρ C, Σ \\
    Ξ ⊢ (Δ||u_k[x_i/y_i] ⇓ Θ||z) :_ρ C, Σ}
  {Ξ ⊢ (Γ||\case[q] e {c_k y_1…y_n ↦ u_k} ⇓ Θ||z) :_ρ C, Σ}
  {\text{case}}


\inferrule
  {Ξ ⊢ (Γ, x:_1 \varid{MB} = ⟨j,0⟩ || k x (j+1) ⇓ Δ||z) :_1 IO_0 A, Σ}
  {Ξ ⊢ (Γ,w:_1 : \varid{World} = j||withMailbox k w ⇓ Δ||z) :_1 IO_0 A, Σ}\text{withMailbox}

\inferrule
  {Ξ ⊢ (Γ||x ⇓ Δ||⟨j,i⟩) :_1 \varid{MB},Σ}
  {Ξ ⊢ (Γ||get x ⇓ Δ,x:_1 \varid{MB} = ⟨j,i+1⟩, y:_1 Packet = p^j_i || (y,z)) :_1 (Packet,\varid{MB}),Σ}\text{get}

\inferrule
  {Ξ ⊢ (Γ||x ⇓ Δ||p^j_i) :_1 Packet,Σ}
  {Ξ ⊢ (Γ||send x ⇓ Δ||()) :_1 (),Σ}\text{send}
  \end{mathpar}
  \caption{Strengthened operational semantics (Omitting the obvious m.abs and m.app for concision)}
  \label{fig:typed-semop}
\end{figure}

A few noteworthy remarks about the semantics in
\fref{fig:typed-semop} can be made. First, the |let| rule does not necessarily
allocate in the garbage collected heap anymore — this was the goal of
the strengthened semantics to begin with — but nor does it
systematically allocate bindings of the form $x :_1 A = e$ in the
linear heap either: the heap depends on the multiplicity $ρ$. The
reason for this behaviour is promotion: an ostensibly linear value can
be used in an unrestricted context. In this case the ownership of $x$
must be given to the garbage collector: there is no static knowledge
of $x$'s lifetime. For the same reason, the linear variable case
requires $ρ$ to be $1$ (Corollary~\ref{cor:linear-variable} will prove
this restriction to be safe).

The other important rule is the |alloc| rule: it requires a result of
the form $\varid{Unrestricted} x$ of multiplicity $1$ while returning a
result of multiplicity $ω$. This constraint is crucial, because the |alloc| rule is the
only rule which makes it possible to use of a linear value in order to produce a
garbage collected value, which in turn justifies that in the ordinary
semantics, queues can be allocated in the linear heap. The reason why
it is possible is that, by definition, in $\varid{Unrestricted} x$, $x$ \emph{must} be
in the garbage-collected heap. In other words, when an expression $e :
\varid{Unrestricted} A$ is forced to the form $\varid{Unrestricted} x$, it will have consumed all the
pointers to the linear heap (the correctness of this argument is
proved in \fref[plain]{lem:type-safety} below).

The crucial safety property of the strengthened relation is that it
preserves well-typing of states.

\begin{lemma}[Strengthened reduction preserves typing]\label{lem:type-safety}
  If  $Ξ ⊢ (Γ||t ⇓ Δ||z) :_ρ A, Σ$, then
  $$
  Ξ ⊢ (Γ||t :_ρ A),Σ \text{\quad{}implies\quad{}} Ξ ⊢ (Δ||z :_ρ A),Σ.
  $$
\end{lemma}
\begin{proof}
  By induction on the typed-reduction.
\end{proof}

Thanks to this property we can freely consider the restriction of the
strengthened relation to well-typed states. For this reason, from now
on, we only consider well-typed states.

\begin{corollary}[Never stuck on the linear variable rule]\label{cor:linear-variable}
  $Ξ ⊢ (Γ,x:_1A=e ||x) :_ωB , Σ$ is not reachable.
\end{corollary}
\begin{proof}
  Remember that we consider only well-typed states because of
  \fref{lem:type-safety}. By unfolding the typing rules it is easy
  to see that $Ξ ⊢ (Γ,x:_1A=e ||x) :_ωB , Σ$ is not well-typed: it
  would require $x:_1 A = ωΔ$ for some $Δ$, which cannot be.
\end{proof}

We are now ready to prove properties of the ordinary semantics by
transfer of properties of the strengthened semantics. Let us start by
defining a notion of type assignment for states of the ordinary
semantics.

\newcommand{\ta}[2]{γ(#1)(#2)}

\begin{definition}[Type assignment]
  A well-typed state is said to be a type assignment for an ordinary
  state, written $\ta{Γ:e}{Ξ ⊢ Γ' || e' :_ρ A , Σ}$, if
  $e=e' ∧ Γ' \leqslant Γ$.

  That is, $Γ'$ is allowed to strengthen some $ω$ bindings to be
  linear, and to drop unnecessary $ω$ bindings.
\end{definition}

Note that for a closed term, type assigment reduces to the fact that
$e$ has a type. So we can see type assignment to state as a
generalisation of type assignment to terms which is preserved during
the reduction. Let us turn to prove that fact, noticing that type
assignment defines a relation between ordinary states and well-typed
states.

\begin{lemma}[Type safety]\label{lem:actual_type_safety}
  The refinement relation defines a simulation of the ordinary
  reduction by the strengthened reduction.

  That is for all $\ta{Γ:e}{Ξ ⊢ (Γ'||e) :_ρ A,Σ}$ such that $Γ:e⇓Δ:z$,
  there exists a well-typed state $Ξ ⊢ (Δ'||z) :_ρ A,Σ$ such that
  $Ξ ⊢ (Γ||t ⇓ Δ||z) :_ρ A, Σ$ and $\ta{Δ:z}{Ξ ⊢ (Δ'||z) :_ρ A,Σ}$.
\end{lemma}
\begin{proof}
  This is proved by a straightforward induction over the ordinary
  reduction. The case of let may be worth considering for the curious
  reader.
\end{proof}

From type-safety, it follows that a completely evaluated program
has necessarily deallocated all the linear heap. This is a form of
safety from resource leaks (of course, resource leaks can always be
programmed in, but the language itself does not leak resources).

\begin{corollary}[Eventual deallocation of linear values]
  Let $w:_1 \varid{World} ⊢ t : \varid{World}$ be a well-typed term. If
  $w :_1 \varid{World} = 0 :t ⇓ Δ: j$, then $Δ$ only contains $ω$-bindings.
\end{corollary}
\begin{proof}
  By \fref{lem:actual_type_safety}, we have $⊢ (Δ||j :_1 \varid{World}), ⋅
  $. Then the typing rules of $\flet$ and $j$ (see
  \fref{sec:model-io}) conclude: in order for $j$ to be well typed,
  the environment introduced by $\flet Δ$ must be of the form $ωΔ'$.
\end{proof}

For the absence of use-after-free errors, let us invoke a liveness
property: namely that the type assignment is also a simulation of the
strengthened semantics by the ordinary semantics (making type
assignment a bisimulation). There is not a complete notion of progress
which follows from this as big step semantics such as ours do not
distinguish blocking from looping: we favour clarity of exposition
over a completely formal argument for progress.

\begin{lemma}[Liveness]\label{lem:liveness}
  The refinement relation defines a simulation of the strengthened
  reduction by the ordinary reduction.

  That is for all $\ta{Γ:e}{Ξ ⊢ (Γ'||e) :_ρ A,Σ}$ such that
  $\ta{Δ:z}{Ξ ⊢ (Δ'||z) :_ρ A,Σ}$, there exists a state $Δ:z$ such
  that $Γ:e⇓Δ:z$ and $\ta{Δ:z}{Ξ ⊢ (Δ'||z) :_ρ A,Σ}$.
\end{lemma}
\begin{proof}
  This is proved by a straightforward induction over the ordinary
  reduction.
\end{proof}

In conjunction with Corollary~\ref{cor:linear-variable},
\fref{lem:liveness} shows that well-typed programs do not get
blocked, in particular that garbage-collected objects \Red{which point to the
linear objects are not dereferenced after the linear object has been
freed:} \calc{} is safe from use-after-free errors.

\section{Applications}
\label{sec:applications}

There is a wealth of literature regarding the application of linear typing to
many practical problems, for instance: explicit memory
management~\cite{lafont_linear_1988,hofmann_in-place_,ahmed_l3_2007},
array
computations~\cite{bernardy_duality_2015,lippmeier_parallel_2016},
protocol specification~\cite{honda_session_1993}, privacy
guarantees\cite{gaboardi_linear_2013}, graphical
interfaces\cite{krishnaswami_gui_2011}.

This section develops a few examples which are directly usable in
\HaskeLL{}, that is simply by changing Haskell's type system, and
using the dynamic semantics of \fref{sec:dynamics} to justify the
memory safety of a foreign heap implemented using a foreign function
interface.


\subsection{Lowering the \textsc{gc} pressure}
\label{sec:lower-gc}

In a practical implementation of the zero-copy packet example of
\fref{sec:packet}, the priority queue can easily become a bottleneck,
because it will frequently stay large. We can start by having a less
obnoxiously naive implementation of queues, but this optimisation would not solve
the issue with which we are concerned with in this section: garbage
collection latency. Indeed, the variance in latency incurred by
\textsc{gc} pauses can be very costly in a distributed application. Indeed,
having a large number of processes which may decide to run a long
pause increases the probability that at least one is running a pause.
Consequently, waiting on a large number of processes is slowed down (by the
slowest of them) much more often than a sequential application. This
phenomenon is known as Little's law~\cite{little_proof_1961}.

One solution to this problem is to allocate the priority queue with
|malloc| instead of using the garbage collector's allocator. Of
course, using |malloc| leaves memory safety in the hand of the
programmer. Fortunately, it turns out that the same arguments that we used
to justify proper deallocation of mailboxes in \fref{sec:dynamics} can
be used to show that, with linear typing, we can allocate a priority
queue with |malloc| safely (in effect considering the priority queue
as a resource). We just need to replace the |empty| queue function from
\fref{sec:packet} by a |withQueue :: (PQ a ⊸ IO a) ⊸ IO a| primitive,
in the same style as |withMailbox|.

We can go even further and allow |malloc|'d queues to build pure values:
it is enough to replace the type of |withQueue| as |withQueue :: (PQ a
⊸ Unrestricted a) ⊸ Unrestricted a)|. Justifying the safety of this
type requires additional arguments as the result of |withQueue| may be
promoted (|IO| action are never promoted because of their |World| parameter),
hence one must make sure that the linear heap is properly emptied,
which is in fact implied by the typing rules for |Unrestricted|.

\subsection{Safe streaming}

The standard for writing streaming applications (\emph{e.g.} reading
from a file) in Haskell is to use a combinator library such as Conduit
or Machines. Such libraries have many advantages: they are fast, they
release resources promptly, and they are safe.

However, they come at a significant cost: they are rather difficult to
use. As a result we have observed companies walking back from this
type of library to use the simpler, but unsafe Streaming library.

The lack of safety of the stream library stems from the |uncons| function (in
|Streaming.Prelude|):
\begin{code}
  uncons :: Monad m => Stream (Of a) m () -> m (Maybe (a, Stream (Of a) m ()))
\end{code}
Note the similarity with the |IO| monad: a stream is consumed and a
new one is returned. Just like the |World| of the |IO| monad, the
initial stream does not make sense anymore and reading from it will
result in incorrect behaviour. We have observed this very mistake in
actual industrial code, and it proved quite costly to hunt
down. \Citet[Section 2.2]{lippmeier_parallel_2016} describe a very
similar example of unsafety in the library Repa-flow.

Provided a sufficiently linear notion of monad (see
\citet[Section 3.3 (Monads)]{morris_best_2016} for a discussion on the
interaction of monads and linear typing), we can make |uncons| safe
merely by changing the arrow to a linear one:
\begin{code}
  uncons :: Monad m => Stream (Of a) m () ⊸ m (Maybe (a, Stream (Of a) m ()))
\end{code}

\subsection{Protocols}

It is well known that concurrent programs can be conveniently encoded
by using continuations~\cite{wand_continuation-based_1980}. By using types, we can additionally verify
that the protocols match: namely, if a program $p$ implements a
protocol $P$, then a program $p'$ intended to communicate with $p$ is given the
dual type ($P^⊥$). In ML-family
languages, the dual can be represented simply by an arrow to to $⊥$:
$P^⊥ = P → ⊥$, where $⊥$ is a type of effects (which include
communication on a channel).  All effectful programs must then use CPS
so they eventually terminate with an effect. An issue of such encoding
is that a continuation can be called several times, which can be
problematic because the order of the protocol is not respected. Thanks
to linear types, we can solve the problem simply by encoding the dual
as a linear arrow: $P^⊥ = P ⊸ ⊥$. Then, the communication between $p$
and $p'$ is guaranteed deadlock-free.

Some programming languages featuring session types have instead native
support negation\cite{wadler_propositions_2012}. For each type constructor there is a dual:
$(A⊕B)^⊥ = A^⊥ \& B^⊥$. Such an approach meshes well with languages
modelled after classical logic.  Instead, the CPS approaches works
better for languages bases on intuitionistic logic, such as
Haskell. Hence we choose not to support duality specially.

The following example gives a glimpse of what linear CPS code may look
like.
\begin{code}
  data A⊕B  = Left :: A ⊸ A⊕B | Right :: B ⊸ A⊕B
  type A&B  = ((A⊸⊥)⊕(B⊸⊥))⊸⊥

if' :: Bool ⊸ (a & a) ⊸ (a ⊸ ⊥) ⊸ ⊥
if' True   p k = p (Left   k)
if' False  p k = p (Right  k)
\end{code}

\section{Related work} \label{sec:related}

\subsection{Regions}

Haskell's |ST| monad~\cite{launchbury_st_1995} taught us a
conceptually simple approach to lifetimes. By equipping |ST| with a
region argument |s| and exposing as the only way to get out of |ST|
the function:
\begin{code}
  runST :: (forall s. ST s a) -> a
\end{code}
the type systems ensures that releasing every resource after |runST|
is safe.

The apparent simplicity (no need to modify the language) turns into a
lot of complications when developed in practice beyond the |ST| monad.
\begin{itemize}
\item The region-based approach enforces a stack discipline for
  allocation and deallocation. In our running example, if mailboxes
  which are not used have to be kept until mailboxes open in there
  scope has been closed, they would be monopolising precious resources
  (typically a socket).
\item It is not easy to mix data for different nested regions, even
  though value from any region could in theory (and sometimes must)
  interact with values from their parent region. For instance, storing
  packets from two different mailboxes in a priority queue. To solve
  this issue \citet{kiselyov_regions_2008} introduced a systematic way
  to lift values from a region to their subregion. But while it solves
  the issue in theory, it is rather hard to use in practice. The
  HaskellR project \todo{cite HaskellR} uses
  \citeauthor{kiselyov_regions_2008}'s regions to safely synchronise values
  shared between two different garbage collectors. The use of HaskellR
  in an industrial setting demonstrated that the lifting to subregions
  imposes an unreasonable burden on the programmer. By contrast, with
  linear types, values in two regions (in our running example packets
  from different mailboxes) have the same type hence can safely be
  mixed: any data structure containing packet of a mailbox will be
  forced to be consumed before the mailbox is closed.
\end{itemize}

\subsection{Finalisers}

An alternate approach to memory safety of resources in
garbage-collected language is to reify the resource as a \emph{proxy
  object} on the \textsc{gc} heap and attach a finaliser to the
proxy. That is, when the garbage collector frees the proxy it is
instructed to perform an action which, in this case, will free the
resource as well.

This is not usually done in practice because, as argued by
\citet{kiselyov_iteratees_2012}, the garbage collector gives no
real-time guarantee for the deallocation of dead data (this is
especially the case for an incremental garbage collector which is
paramount in low-latency applications). This causes a form a resource
leak, where scarce resources may be rendered unavailable for a long time.

\subsection{Uniqueness types}

A large chunk of the literature deals with linearity not by using linear types,
but instead by using uniqueness (or ownership) types. The most prominent representatives of
languages with such uniqueness types are perhaps Clean \todo{Cite Clean} and
Rust~\cite{matsakis_rust_2014}. \HaskeLL, on the other hand, is
designed around linear types based on linear
logic~\cite{girard_linear_1987}.


There is a form of duality between the two: linear typing ensures
that linear functions use their argument once,
while the context can share a linear argument as many times as it pleases; while uniqueness
typing ensures that the argument of a function is not where with anywhere
else in the context, but the function can use it as it pleases (with
some caveat).

From a compiler's perspective, uniqueness type provide a non-aliasing
analysis while linear types provides a cardinality analysis. The
former aims at in-place updates and related optimisations, the latter
at inlining and fusion. Rust and Clean largely explore the
consequences of uniqueness on in-place update; an in-depth exploration
of linear types in relation with fusion can be found
in~\citet{bernardy_composable_2015}, see also the discussion in
\fref{sec:fusion}.

Several points guided our choice of designing \HaskeLL{} around linear
logic rather than uniqueness types: 1. functional languages have more use
for fusion than in-place update (\textsc{ghc} has a cardinality
analysis, but it does not perform a non-aliasing analysis); 2 with modern computer architectures in-place update is no longer crucial for performance (accessing RAM requires making copies anyway); 3. there is a
wealth of literature detailing the applications of linear
logic — see \fref{sec:applications}; 4. and desicively, linear type systems are
conceptually simpler than uniqueness type systems, which gives a
clearer path to implementation in \textsc{ghc}.

\subsection{Linearity as a property of types vs. a property of bindings}

In several presentations \cite{wadler_linear_1990,mazurak_lightweight_2010,morris_best_2016}
programming languages incorporate
linearity by dividing types into two kinds. A type is either linear
or unrestricted.

In effect, this imposes a clean separation between the linear world
and the unrestricted world. An advantage of this approach is that it
instantiate both to linear types and to uniqueness types depending on
how they the two worlds relate, and even have characteristics of
both\cite{devries_linearity_2017}.

Such approaches have been very successful for theory: see for instance
the line of work on so-called \emph{mixed linear and non-linear logic}
(usually abbreviated \textsc{lnl}) started by
\citet{benton_mixed_1995}. However, for practical language design,
code duplication between the linear an unrestricted worlds quickly
becomes costly. So language designer try to create languages with some
kind of kind polymorphism to overcome this limitation. This usually
involves a subkinding relation and bounded polymorphism. This kind
polymorphic designs are rather complex. See \citet{morris_best_2016}
for a recent example. By contrast, the type system of \calc{} is quite
straightforward.

Another point, rather specific to \textsc{ghc}, is that the kind
system of \textsc{ghc} is quite rich, with support for impredicative
dependent types, and a wealth of unboxed or otherwise primitive types
which can't be substituted for polymorphic type arguments. It is not
clear how to support linearity in \textsc{ghc} by extending its kind system.
In contrast, our design inherits many features of \citeauthor{mcbride_rig_2016}'s,
including its compatibility with dependent types, and
such compatibility is pretty much necessary to accommodate the dependently-typed kinds of \textsc{ghc}.

\subsection{Alms}
Alms~\cite{tov_practical_2011} is an \textsc{ml}-like language based on affine types (a variant
of linear types where values can be used \emph{at most} once). It is
uses the kinds to separate affine from unrestricted arguments.

It is a case in point for kind-based systems being more complex: for
the sake of polymorphism, Alms deploys an elaborate dependent kind
system. Even if such a kind system could be added to an existing
language implementation, Alms does not attempt to be backwards
compatible with an \textsc{ml} dialect. In fact
\citeauthor{morris_best_2016} notes:
\begin{quote}
  Despite the (not insignificant) complexity of [Alms], it is still
  not clear that it fully supports the expressiveness of traditional
  functional programming languages. For example, [Alms] has distinct
  composition operators with distinct types. These types are not
  related by the subtyping relation, as subtyping is contravariant in
  function arguments.
\end{quote}

\subsection{Rust}

Already mentioned above is the language
Rust~\cite{matsakis_rust_2014}, based on ownership types. This
distinction notwithstanding, Rust's type system resembles the original
presentation of linear logic where every type $A$ represent linear
values, unrestricted values at type $A$ have a special type $!A$, and
duplication is explicit.

In a sense, Rust quite beautifully solves the problem of being mindful
about memory, resources, and latency. But this comes at a heavy price:
Rust, as a programming language, is specifically optimised for writing
programs that are structured using the RAII
pattern\footnote{\url{https://en.wikipedia.org/wiki/Resource_acquisition_is_initialization}}
(where resource lifetimes are tied directly or indirectly to stack
allocated objects that are freed when the control flow exits the
current lexical scope). Ordinary functional programs seldom fit this
particular resource acquisition pattern so end up being second class
citizens. For instance, tail recursions, so dear to the functional
programmer's heart, can usually not be eliminated, as resource
liberation must be triggered when the tail call returns.

\HaskeLL{} aims to hit a different point in the design space where
regular Haskell programs are the norm, hence are optimised for, and we
can, at the cost of extra effort, be mindful about memory and latency.

\subsection{Related type systems}

The \calc{} type system is heavily inspired from the work of
\citet{ghica_bounded_2014} and \citet{mcbride_rig_2016}. Both of them
present a type system where arrows are annotated with the multiplicty
of the the argument that they require, and where the multiplicities
form a semi-ring.

In contrast with \calc, \citeauthor{mcbride_rig_2016} uses a
multiplicity-annotated type judgement $Γ ⊢_ρ t : A$. Where $ρ$
represents the multiplicity of $t$. So, in
\citeauthor{mcbride_rig_2016}'s system, when an unrestricted value is
required, instead of computing $ωΓ$, it is enough to check that
$ρ=ω$. The problem is that this check is arguably too coarse, and
results into the judgement $⊢_ω λx. (x,x) : A ⊸ (A,A)$ being derivable.
This derivation is not desirable: it means that there cannot be
reusable definitions of linear functions. In terms of linear logic~\cite{girard_linear_1987},
\citeauthor{mcbride_rig_2016} makes the natural arrow $!(A⊸B) ⟹ !A⊸!B$
invertible.

In that respect, our system is closer to
\citeauthor{ghica_bounded_2014}'s. What we keep from
\citeauthor{mcbride_rig_2016}, is the typing rule of |case| (see
\fref{sec:statics}), which can be phrased in terms of linear logic as
making the natural arrow $!A⊗!B ⟹ !(A⊗B)$\unsure{Should we use the
  notations from the article here? |Unrestricted| and |(,)|} invertible. This choice is
unusual from a linear logic perspective, but it is the key to be able
to use types both linearly an unrestrictedly without intrusive
multiplicity polymorphic annotation on all the relevant types.

The literature on so-called
coeffects~\cite{petricek_coeffects_2013,brunel_coeffect_core_2014}
uses type systems similar to \citeauthor{ghica_bounded_2014}, but
with a linear arrow and multiplicities carried by the exponential
modality instead. \Citet{brunel_coeffect_core_2014}, in particular,
develops a Krivine realisability model for such a calculus. We are not
aware of an account of Krivine realisability for lazy languages, hence
it is not directly applicable to \calc.

\subsection{Operational aspects of linear languages}

Recent literature is surprisingly quiet on the operational aspects of
linear types, and rather concentrates on uniqueness types
\cite{pottier_programming_2013,matsakis_rust_2014}.

Looking further back, \citet{wakeling_linearity_1991} produced a
complete implementation of a language with linear types, with the goal
of improving the performance. Their implementation features a separate
linear heap, as \fref{sec:dynamics} where they allocate as much as
possible in the linear heap, as modelled by the strengthened
semantics. However, \citeauthor{wakeling_linearity_1991} did not
manage to obtain consistent performance gains. On the other hand, they
still manage to reduce \textsc{gc} usage, which may be critical in
distributed and real-time environments. Thus the trade-off is
beneficial is certain situations.

Regarding absolute performance increase,
\citeauthor{wakeling_linearity_1991} propose not attempt prompt free
of thunks, and instead take advantage of linear arrays. In this paper,
we go further and leave the management of external (linear) data to
external code, only accessing it via an API. Yet, our language
supports an implementation where each individual constructor with
multiplicity 1 can be allocated on a linear heap, and deallocated when
it is pattern matched. Implementing this behaviour is left for future work.

\section{Conclusion and future work}

This article demonstrates how an existing lazy language, such
as Haskell, can be extended with linear types, without compromising
the language, in the sense that:
\begin{itemize}
\item Existing programs are valid in the extended language
  \emph{without modification}.
\item Such programs retain the same semantics.
\item The performance of existing programs is not affected.
\end{itemize}
In other words: regular Haskell comes first. Additionally, first-order
linearly typed functions and data structures are usable directly from
regular Haskell code. In such a situation their semantics is that of
the same code with linearity erased.

Furthermore \calc{} has a particularly non-invasive design, and thus
it is possible to integrate with an existing mature compiler. We are
developing a prototype implementation extending \textsc{ghc} with
multiplicities. The main difference between the implementation and
\calc, is that the implementation adopts some level of
bidirectionality: typing contexts go in, actual multiplicities come
out (and are compared to their expected values). As we hoped, this
design integrates very well in \textsc{ghc}.

It is worth stressing that, in order to implement foreign data
structures like we have advocated, in this article, as a means to
provide safe access to resources or reduce \textsc{gc} pressure and
latency, we only need to modify the type system: primitives to
manipulate foreign data can be implemented in libraries using the
foreign function interface. This helps make the prototype quite lean.

\subsection{Dealing with exceptions}
Exceptions run afoul of linearity. Consider for instance the
expression |error "oops" + x|, for some linear |x|. Evaluating |x| may
be required in order to free resources, but |x| will not be evaluated,
hence the resources will linger.

Haskell program can raise exceptions even during the evaluation of
pure code~\cite{peyton_jones_exceptions_1999}, so we have to take it
into account in order to demonstrate the eventual deallocation of
resources. Both \citet{thrippleton_memory_2007} and
\citet{tov_theory_2011} develop solutions, but they rely on effect
type systems which probably require too much change to an existing
compiler. Additionally, effect type systems would not be compatible
with Haskell's asynchronous exception
mechanism~\cite{marlow_async_exceptions_2001}.

Because we are using explicit allocators for resources such as
|withMailbox :: (MB ⊸ IO a) ⊸ IO a|. These allocators can be
responsible for safe deallocation in response to exceptions,
internally making use of the bracket operation~\cite[Section
7.1]{marlow_async_exceptions_2001}. A full justification of this fact
is left for future work.

\subsection{Fusion}
\label{sec:fusion}

Inlining is a staple of program optimisation exposing opportunities
for many program transformation including fusion. Not every function
can be inline without negative effects on performance: inlining a
function with two use sites of the argument may result in duplicating
a computation.

In order to discover inlining opportunities \textsc{ghc} deploys a
cardinality analysis~\cite{sergey_cardinality_2014} which determines
how many times function uses their arguments. The limitation of such
an analysis is that it is necessarily heuristic (the problem is
undecidable). Consequently, it can be hard for the programmer to rely
on such optimisations: a small, seemingly innocuous change can prevent
a critical inlining opportunity and have rippling effects throughout
the program. Hunting down such a performance regression proves very
painful in practice.

Linear types can address this issue and serve as a programmer-facing
interface to inlining: because it is always safe to inline a linear
function, we can make it part of the \emph{semantics} of linear
functions that they are always inlined. In fact, the system of
multiplicity annotation of \calc{} can be faithfully embedded the
abstract domain presented by \citet{sergey_cardinality_2014}. This
gives confidence in the fact that multiplicity annotation can serve as
cardinality \emph{declarations}.

Formalising and implementing the integration of multiplicity
annotation in the cardinality analysis is left as future work, as it
requires a significant effort.

\subsection{Extending multiplicities}

For the sake of this article, we use only $1$ and $ω$ as
possibilities.  In fact, \calc{} can readily be extended to more
multiplicities: we can follow \citet{ghica_bounded_2014} and
\citet{mcbride_rig_2016} which work with abstract sets of
multiplicities.  In particular, in order to support dependent types,
we additionally need a $0$ multiplicity.

Applications of multiplicities beyond linear logic seem to often have
too narrow a focus to have their place in a general purpose language
such as Haskell. \Citet{ghica_bounded_2014} propose to use
multiplicities to represent real time annotations, and
\citet{petricek_coeffects_2013} show how to use multiplicities to
track either implicit parameters (\emph{i.e.} dynamically scoped
variables) or the size of the history that a dataflow program needs to
remember. Of these, only the implicit parameters may be of relevance
to Haskell, but even so, it is probably not desirable.

Nevertheless, more multiplicities may prove useful. For instance we
may want to consider a multiplicity for affine arguments (\emph{i.e.}
arguments which can be used \emph{at most once}).

The general setting for \calc{} is an ordered-semiring of
multiplicities (with a join operation for type inference). The rules
are mostly unchanged with the \emph{caveat} that $\mathsf{case}_q$
must exclude $q=0$ (in particular we see that we cannot
substitute multiplicity variables by $0$). The variable rule is
modified as:
$$
\inferrule{ x :_1 A \leqslant Γ }{Γ ⊢ x : A}
$$
Where the order on contexts is the point-wise extension of the order
on multiplicities.


\bibliography{../PaperTools/bibtex/jp.bib,../local.bib}{}
\bibliographystyle{ACM-Reference-Format.bst}

\end{document}
% Local Variables:
% ispell-local-dictionary: "british"
% End:

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
%  LocalWords:  unannotated tuple subkinding invertible coeffects
%  LocalWords:  unrestrictedly bidirectionality GADT reify finaliser
%  LocalWords:  Finalisers
