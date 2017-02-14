% -*- latex -*-

% (1) Horrible, terrible, 1 column format.  111 characters in a line; bad on the eyes.
\documentclass[acmlarge,dvipsnames,natbib]{acmart}

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
%subst keyword a = "\mathsf{" a "}"
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
% TODO: \newcommand*{\fancyreflemlabelprefix}{lem}
\def\frefsecname{Section}
\def\freffigname{Figure}
\def\frefdefname{Definition}
\def\Frefdefname{Definition}
\def\freflemname{Lemma}
\def\Freflemname{Lemma}
\def\fancyrefdeflabelprefix{def}
\frefformat{plain}{\fancyrefdeflabelprefix}{{\frefdefname}\fancyrefdefaultspacing#1#2}
\Frefformat{plain}{\fancyrefdeflabelprefix}{{\Frefdefname}\fancyrefdefaultspacing#1#2}
\def\fancyreflemlabelprefix{lem}
\frefformat{plain}{\fancyreflemlabelprefix}{{\freflemname}\fancyrefdefaultspacing#1#2}
\Frefformat{plain}{\fancyreflemlabelprefix}{{\Freflemname}\fancyrefdefaultspacing#1#2}

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
\newcommandx{\improvement}[2][1=]{\todo[linecolor=Plum,backgroundcolor=Plum!25,bordercolor=Plum,#1]{#2}}
\newcommandx{\resolved}[2][1=]{\todo[linecolor=OliveGreen,backgroundcolor=OliveGreen!25,bordercolor=OliveGreen,#1]{#2}} % use this to mark a resolved question
\newcommandx{\thiswillnotshow}[2][1=]{\todo[disable,#1]{#2}} % will replace \resolved in the final document

% Peanut gallery comments by Ryan:
\newcommandx{\rn}[1]{\todo[]{RRN: #1}}

% Link in bibliography interpreted as hyperlinks.
\newcommand{\HREF}[2]{\href{#1}{#2}}

% \newtheorem{definition}{Definition}
% \newtheorem{lemma}{Lemma}
\newtheorem{remark}{Remark}

\newcommand\calc{{\ensuremath{λ^q}}}

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

% Title portion

% Put working title proposals here:
% \title{\HaskeLL}
% \title{\HaskeLL: Linear types with backwards compatibility in an established language}
% \title{\HaskeLL: Linear types with Backwards Compatibility}
\title{\HaskeLL: Systems Programming with \\ Backwards-Compatible Linear Types}
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
\author{Arnaud Spiwack}
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


\begin{abstract}
  \todo{Expand}
  This article introduces and describes a
  linearly-typed lazy programming language which is designed to be
  integrate well with an existing programming language, in particular
  in GHC/Haskell.
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

% \thanks{This work is supported by FIXME (for de-anonymised version only) }


\maketitle

% The default list of authors is too long for headers}
% \renewcommand{\shortauthors}{G. Zhou et. al.}

\section{Introduction}

Can we use Haskell to implement a low-latency server that caches a large dataset
in memory?  Today, the answer is a clear
``no''\footnote{\Red{{URL-of-reddit-discussion}}}.  The GC pauses are
unacceptable (and would remain so even with incremental GC).
%
This application requires minimizing GC pauses by managing the largest heap data
structures outside of the regular heap.  Traditionally, programmers resort to
pushing the data off-heap manually, accessing it through FFI calls.  But this
common technique poses a safety risk to {\em clients} of the data structure, who may
commit use-after-free errors.  Much better would be a type-safe solution.
% that stays within the high-level language.

Indeed, type systems can be useful for controlling resource usage, not just
ensuring correctness.  Affine types~\cite{finishme}, linear
types~\cite{finishme}, permission types \cite{finishme}, and fractional
permissions \cite{finishme} enable safe manual memory management as well as safe
handling of scarce resources such as sockets and file handles.  All these
approaches are heavily researched, yet these ideas have had relatively little
effect on programming practice.  Few practical, full-scale languages are
designed from the start with such features.  Rust is the major
exception~\cite{matsakis_rust_2014}, and in Rust we see one of the attendant
complications: adding advanced resource-tracking features puts a burden on
language learners, who pass through an initiation period, ``fighting the borrow
checker''.

Why can't more languages add linear or affine types?  Unfortunately, there has
not been a clear path to augment preexisting type systems without (1) breaking
existing code, and (2) forcing the feature on users who don't need it, as in the
case of Rust.
% 
Recent work~\cite{best-of-both-worlds} has come closer to unifying linear and
unrestricted code, avoiding the need to {\em duplicate} basic library functions
like compose ($\circ$) or append (|++|) to add incompatible linear versions.
But this approach still divides all types into unrestricted and linear, and adds
constraints on linearity status to the types of standard
combinators~---~constraints and complications which the newcomer to the language
could not easily ignore, were basic library functions augmented in this way.

We propose a design that leaves most types, such as |Int|, unmodified, and
instead associates linearity with {\em binders}, such as ``$\flet x :_{1} T =
\dots$'', indicating that $x$ must be used exactly once in the body.
%
We say that |x| is bound to a {\em linear value}, but |x| does not have a linear
{\em type}.
%
Only function types change to include (optional) linearity.  Even linear
functions support {\em backwards compatibility} by implicit conversion of
arguments at function call sites.  (The intuition is that if {\em any} number of
uses is valid, then exactly one use is permitted.)

We call the extended type system \HaskeLL{} --- Haskell meets Linear Logic ---
and with it we can enrich standard Haskell Prelude types such as |map| and |++|,
adding, but not requiring, the possibility of linear uses of those functions.
Existing function applications, such as |xs ++ ys|, continue to typecheck as
before, {\em unless} the inputs happen to be linear values.
% 
Indeed, with this approach, a programmer may not need to learn about linearity
to use linear functions, and they may not even {\em see} linearity information
unless the appropriate language extension is enabled.

We make the following contributions:

\begin{itemize}
\item We formalize \HaskeLL{} as \calc{}, a linearly-typed extension of the
  $λ$-calculus with data types, and give its type system (\fref{sec:statics}),
  highlighting how it is compatible with all existing Haskell features,
  including Haskell's \Red{kind system, constraints, GADTs, and even dependent types}.

\item We provide a dynamic semantics for \calc{}, which is unusual,
  combining laziness with explicit deallocation of linear data.  In
  \fref{sec:dynamics} we prove type safety, and, further, that every
  linear value is eventually deallocated, and never referenced after
  it is deallocated.

\item We perform a case study of a low-latency in-memory server (\fref{sec:eval})
  implemented using our type system.  We do not yet modify the GHC memory
  manager, rather, we show how linear types can make FFI-based implementations
  safe.
  
\end{itemize}


%% \note{In interactive low-latency systems (web servers, graphical user
%%   interfaces, high-speed trading systems, real-time analytics and query
%%   services, games, etc), pausing threads performing useful work is
%%   problematic. Because these pauses can happen at any time, for indeterminate
%%   periods of time, an unbounded number of times, the tail-end of runtime
%%   distributions increases.}

%% \note{The latency observed on this use-case caused Pusher to walk away from
%%   Haskell\footnote{\url{https://blog.pusher.com/golangs-real-time-gc-in-theory-and-practice/}}.}



\section{A taste of \HaskeLL}
\label{sec:programming-intro}
Before diving into the technical details, let us give an overview of
\HaskeLL, the proposed design for extending Haskell with linear types,
by means of a number of examples.

Firstly, along with the usual arrow type for intuitionistic functions,
we propose an additional arrow type for linear arrows, written
$A ⊸ B$. In the body of a linear function, the type system tracks that
there is exactly one copy of the parameter available.

\begin{code}
f :: A ⊸ B
f x = {- |x| has multiplicity $1$ here -}
\end{code}

We say that the \emph{multiplicity} of |x| is $1$ in the body of |f|. Similarly, we say
that unrestricted (non-linear) parameters have multiplicity $ω$ (usable
\emph{any finite number} of times, including zero). We also call
functions linear if they have type $A ⊸ B$ and unrestricted if they
ahave $A → B$.

To clarify the meaning of multiplicities, here are the rules for what is allowed
at call sites:
\begin{enumerate}

\item An unrestricted (multiplicity $ω$) value 
  \begin{enumerate}
  \item {\bf can} be passed to a linear function.
  \item {\bf can} be passed to a unrestricted function.  
  \item {\bf can} be returned by a linear function.
  \item {\bf can} be returned by a unrestricted function.    
  \end{enumerate}  

\item A linear (multiplicity $1$) value
  \begin{enumerate}
  \item  {\bf can} be passed to a linear function.
  \item  {\bf cannot} be passed to a unrestricted function.
  \item  {\bf can} be returned by a linear function (and
     the type-system guarantees that it can be promoted to a unrestricted
     value when the function is called in an unrestricted context).
  \end{enumerate}

% RRN: This looks like a duplicate:
% \item A linear value {\bf can} be returned by a linear function.

\end{enumerate}

Indeed, when we say that a function is linear, we refer to its domain,
not its co-domain. Hence, linearity of a function does not influence
what it can return, only what it can take as arguments.

The same examples can be expressed in code: the function |g| below
admits the following implementations, but not the last one:
\begin{code}
f :: a ⊸ a
g :: (Int ⊸ Int -> r) -> Int ⊸ Int -> r

g k x y = k (f x) y      -- Valid
g k x y = k x (f y)      -- Valid
g k x y = k x y          -- Valid
g k x y = k y x          -- Invalid, x has multiplicity 1
\end{code}
\rn{Would be nice to introduce let here and do this in terms of let.}

%% \begin{code}
%% let x : _ 1 A = ... in blah
%% \end{code}

Linear values can be construed as containing {\em resources} which must be
deallocated explicitly, hence can be subject to use-after-free
errors. A file handle may be such a resource, though in this article
we will focus on data stored on a foreign heap. The linear type system
of \HaskeLL{} will ensure both that the deallocation will happen, and
that no use-after-free error occurs.

\subsection{Calling contexts}
\note{Explain calling context here.}



\subsection{Linear data types}

Using the new linear arrow, we can define a linear version of the list
type, as follows:
\begin{code}
data List a where
  []   :: List a
  (:)  :: a ⊸ List a ⊸ List a
\end{code}
That is, given a list |xs| with multiplicity $1$,
yield the elements of |xs| will multiplicity $1$.
Thus the above list
may contain resources without compromising safety: that is, the
resources in |xs| will be eventually deallocated and will not be used
after that.

Many list-based functions conserve the multiplicity of data, and thus can
be given a more precise type. For example we can write |(++)|
as follows:
\begin{code}
(++) :: List a ⊸ List a ⊸ List a
[]      ++ ys = ys
(x:xs)  ++ ys = x : (xs ++ ys)
\end{code}
The type of |(++)| tells us that if we have a list |xs| with
multiplicity $1$, appending any other list to it will never duplicate
any of the elements in |xs|, nor drop any element in |xs|.

A major benefit of \HaskeLL{} is that one can write linear code
whenever it is possible, and use it in unrestricted contexts
anyway. That is, in \HaskeLL{}, giving a more precise type to |(++)|
strengthens the contract that the implementation of |(++)| must
satisfy, but it does not restrict its usage. That is, it is perfectly
legal to provide an |xs| of multiplicity $ω$ to |(++)| ($1$ is, after
all, a finite multiplicity). If both |xs| and |ys| have multiplicity
$ω$, |xs++ys| is \emph{promoted} to multiplicity $ω$. In terms of resources,
if neither |xs| nor |ys| can contain resources,
neither can |xs++ys|: it is thus safe to share |xs++ys|.
%
If |xs| has multiplicity $ω$ and |ys| has multiplicity 1, then
|xs++ys| has only multiplicity 1, and |xs| is being used only once, which is valid.

For an existing language, being able to strengthen |(++)| in a {\em
  backwards-compatible} way is a major boon.
%
Of course, not all functions are linear: a function may legitimately
demand unrestricted input, even to construct an output with
multiplicity $1$. For example the argument of the function repeating its input
indefinitely needs to be unrestricted:
\begin{code}
  cycle :: List a → List a
  cycle l = l ++ cycle l
\end{code}

\subsection{Reachability invariant}
A consequence of the above design is that unrestricted objects never
point to (or contain) linear objects. (But the converse is possible.)
One can make sense operationally of this rule by appealing to
garbage collection: when an unrestricted object is reclaimed by GC,
it would leave all resources that it points to unaccounted
for. Conversely a pointer from a resource to the heap can simply act
as a new GC root. We prove this invariant in \fref{sec:dynamics}.

\subsection{Higher-order linear functions: explicit multiplicity quantifiers}

As seen above, implicit conversions between multiplicities make first-order
linear functions {\em more general}. Higher-order code is more complex; so we
introduce {\em multiplicity polymorphism} as a way to preserve effective code sharing
of higher-order functions. For example, the standard |map| function over
(linear) lists:
\begin{code}
map f []      = []
map f (x:xs)  = f x : map f xs
\end{code}
can be given the two following incomparable types:
\begin{code}
  (a ⊸ b) -> List a ⊸ List b
\end{code}
and
\begin{code}
  (a -> b) -> List a -> List b
\end{code}

\HaskeLL{} generalises over linear and unrestricted arrows with the
syntax $A →_ρ B$. Therefore, |map| can be given the following
most general type:
\begin{code}
  ∀ρ. (a -> _ ρ b) -> List a -> _ ρ List b
\end{code}
%
Likewise, function composition can be given the following type:
\begin{code}
(∘) :: forall π ρ. (b → _ π c) ⊸ (a → _ ρ b) → _ π a → _ (ρ π) c
(f ∘ g) x = f (g x)
\end{code}
That is: two functions of accepting arguments of arbitrary
multiplicities respectively $ρ$ and $π$ can be composed into a
function accepting arguments of multiplicity $ρπ$ (\emph{i.e.} the
product of $ρ$ and $π$ --- see \fref{def:equiv-mutiplicity}).

\subsection{Linearity of constructors}
\label{sec:linear-constructors}

Constructors add their own bit of depth to this story. The design of
\HaskeLL{} advocates treating data-type constructors as linear by
default (that is, all of their arguments are linear). However,
contrary to plain functions, linear constructors are not more general
than constructors with unrestricted arguments.

In \fref{sec:statics}, we will take the necessary step to make sure
that linear constructors correspond to regular Haskell data types when
restricted to the pure (non-linear) Haskell fragment. But even so,
constructors with unrestricted arguments add expressiveness to
\HaskeLL{}. The following data type is the prototypical example of
data type with non-linear constructors\footnote{The type constructor
  |Bang| is in fact an encoding of the so-called \emph{exponential}
  modality written ${!}$ in linear logic.}:
\begin{code}
  data Bang a where
    Bang :: a → Bang a
\end{code}
\improvement{rename |Bang| \emph{e.g.} into |Unrestricted|} The |Bang|
data type is used to indicate that a linear function returns results
with multiplicity $ω$. Such data types are, in fact, the only way to
signify unrestricted results. For example, the following function
effectively turns a boolean with multiplicity 1 into a boolean with
multiplicity $ω$:
\begin{code}
  copy :: Bool ⊸ Bang Bool
  copy True   = Bang True
  copy False  = Bang False
\end{code}
We stress that the above is not the same as the linear identity
function, |id :: Bool ⊸ Bool|. Indeed, |id| conserves the multiplicity
of |Bool| even when it is promoted, whereas |copy| \emph{always}
returns an unrestricted value, regardless of the multiplicity of
its argument.

\subsection{A GC-less queue API}
\label{sec:queue-api}
With linear types, it is possible to write a {\em pure} and {\em
  memory-safe} API for managing any external resource which cannot be
duplicated. An important class of such a resource is foreign C
data. Indeed, since linear data must be used \emph{exactly once}, it
means that such data is statically guaranteed to eventually be
consumed by the program (eventual deallocation) and that the data
cannot be referred to after being consumed (freedom from
use-after-free or free-after-free bugs).

Concretely, operations that do not free the data structure return a
new copy of the data structure (which may, in actuality, reuse and
update the original). For instance, pushing in a queue would have the
following type:
\begin{code}
push :: Msg -> Queue ⊸ Queue
\end{code}
While the |pop| function would be endowed with the following type:
\begin{code}
  pop :: Queue ⊸ Maybe (Bang Msg,Queue)
\end{code}
In the case where there is no value left, no queue is returned,
therefore |pop| must free the queue when its empty. Linear typing will
ensure that we eventually end up popping from the empty queue. As an
exercise, we can define a free function by repeatedly popping a queue
until it is empty:
\begin{code}
  free :: Queue ⊸ ()
  free q = case pop q of
    | Just (q',Bang _m) -> free q'
    | Nothing -> ()
\end{code}

While this example is rather minimal and lends itself to many
optimisations beyond keeping the data off the garbage-collected heap,
it illustrates a real problem in the writing of low-latency Haskell
applications: long-lived data kept in memory (in particular linked
data structures) cause long \textsc{gc} pauses as the pointers must be
traversed and the data copied during collection.\todo{link to or
  replace by the discussion on experimental results}

What linear types bring to this picture is the ability to keep this
data on a foreign heap~—~typically allocated with
\verb+malloc()+~—~hence costing nothing in terms of \textsc{gc}
pressure, while retaining the memory-safety afforded by Haskell's type
system.

The complete \textsc{api} for a linearly typed queue allocated on a
foreign heap could be the following:
\begin{code}
alloc   :: (Queue ⊸ Bang a) ⊸ a
push    :: Msg -> Queue ⊸ Queue
pop     :: Queue ⊸ Maybe (Bang Msg, Queue)
\end{code}
There are a few things going on in this API:
\begin{itemize}
\item The |alloc| function opens a new scope, delimited by the dynamic
  extent of its argument function. This function is provided a fresh
  queue, allocated in the foreign heap (for example using
  \verb|malloc()|).  As enforced by the type-system, this queue must
  be used exactly once.  The return type of the argument function is
  |Bang a|, ensuring that no linear value can be returned: in
  particular the |Queue| must be consumed. (Recall the reachability
  invariant: |Bang| cannot contain a linear object.)

\item Messages of type |Msg| are unrestricted Haskell values managed
  by the garbage collector. They are \emph{copied} into the queue by
  |push| so that the garbage collected version of the message may be
  collected as the version inside the queue survives. Conversely,
  |pop| will copy the message from the queue into the
  garbage-collected heap. The hypothesis is that while there is a very
  large amount of message inside the queue, there will be, at any
  given time, very few messages managed by the garbage
  collector. Because these objects will typically be short-lived, they
  will not normally survive a ``generation 0'' collection, hence
  contribute next to nothing to the \textsc{gc} pressure.

\item Because the queue allocated by |alloc| must be consumed before
  reaching the end of the scope, |pop| must be called and eventually
  return |Nothing|. Indeed, there is no other way to properly get rid
  of the queue. Calling any of the other linear functions does
  ``consume'' the queue, but returns a new one, along with the
  obligation of getting rid of this new queue.
\end{itemize}

\improvement{Write an implementation of queue using \textsc{ffi}
  calls, together with small Haskell wrappers to handle the
  serialisation/copy of messages}

\section{\calc{} statics}
\label{sec:statics}
In this section we turn to the calculus at the core of \HaskeLL{}, namely
\calc{}, and give a step by step account of its syntax and typing
rules.

In \calc{}, objects
\rn{Why ``objects''?  Why not ``values''?}
are classified into two categories: \emph{linear} objects,
which must be used \emph{exactly once} on each code path, and
\emph{unrestricted} objects which can be used an arbitrary number of
times (including zero).

The best way to think of a linear object is to see it as an object
that need not be controlled by the garbage collector: \emph{e.g.}
because they are scarce resources, because they are controlled by
foreign code, or because this object will not actually exist at run
time because it will be fused away. 
\rn{Currently this is the 1st mention of fusing}
The word \emph{need} matters here:
because of polymorphism, it is possible for any given linear object to
actually be controlled by the garbage collector, however, for most
purposes, it must be treated as if it it were not.

This framing drives the details of \calc{}. In particular unrestricted
objects cannot contain linear objects,
because the garbage collector needs to
control transitively the deallocation of every sub-object: otherwise we may
have dangling pointers or memory leaks. On the other hand it is
perfectly fine for linear objects to refer to unrestricted objects.
\rn{Well, ``perfectly fine'' means ``expensive pinning'' in this case, to amke
  them GC roots.}
So any
object containing a linear object must also be linear. Crucially this property
applies to closures as well (both partial applications and lazy
thunks): \emph{e.g.} a partial application of a function to a linear
object is, itself, a linear object (which means that such
a partial application must be applied exactly once).
More generally, the application of a function
to a linear object is linear, since it is, in general, a lazy
thunk pointing to that linear object. (In fact, even in a strict
language, the result may contain the linear argument and so must be
linear.)

\subsection{Typing contexts}
\label{sec:typing-contexts}

\rn{I would like to switch this with 3.2.  Jumping right into typing contexts
is... well, lacking context.  It would be better to first understand why/where
we need to add and scale contexts.}

In \calc{}, each variable in typing contexts is annotated with a
multiplicity.
Concrete multiplicities are either $1$ or $ω$ which stand for linear
and unrestricted bindings, respectively. For the sake of
polymorphism, multiplicities are extended with multiplicity
\emph{expressions}, which contain variables (ranged over by the
metasyntactic variables \(π\) and \(ρ\)), sum\improvement{We use sums
  nowhere in the examples; shall we remove this? -- [Aspiwack] in the
  case of $1$/$ω$ multiplicity $π+ρ$ is always (implicitly) $ω$, so
  there may indeed be no benefit to formal sums in the scope of this
  paper}, and product. The complete syntax of multiplicities and
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
\subsection{Typing}

The static semantics of \calc{} is expressed in terms of the
familiar-looking judgement \(Γ ⊢ t : A\). Its meaning however, may be
less familiar. The judgement \(Γ ⊢ t : A\) ought to be read as
follows: the term $t$ builds \emph{exactly one} $A$, and consumes all
of $Γ$, with the multiplicities specified.  This section precisely defines the
typing judgement.

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
One may thus expect the type $A⊸B$ to be a subtype of $A→B$, however
this does not hold, for the mere reason that there is no notion of
subtyping in \calc{}. Indeed, our objective is to integrate with
Haskell, which is based on Hindley-Milner-style
polymorphism, and subtyping and polymorphism do not mesh well.
Thus \calc{} is based on polymorphism rather than subtyping.

Data type declarations, also presented in \fref{fig:syntax},
deserve some additional explanation.
\begin{align*}
  \data D  \mathsf{where} \left(c_k : A₁ →_{q₁} ⋯    A_{n_k} →_{q_{n_k}} D\right)^m_{k=1}
\end{align*}
The above declaration means that \(D\) has \(m\) constructors
\(c_k\), for \(k ∈ 1…m\), each with \(n_k\) arguments. Arguments of
constructors have a multiplicity, just like arguments of functions:
an argument of multiplicity $ω$ means that the data type can store,
at that position, data which \emph{must} have multiplicity $ω$;
while a multiplicity of $1$ means that data at that position
\emph{can} have multiplicity $1$ (or $ω$). A further requirement is
that the multiplicities $q_i$ must be concrete (\emph{i.e.} either
$1$ or $ω$).

For most purposes, $c_k$ behaves like a constant with the type
$A₁ →_{q₁} ⋯ A_{n_k} →_{q_{n_k}} D$. As the typing rules of
\fref{fig:typing} make clear, this means in particular that from a an
object $d$ of type $D$ with multiplicity $ω$, pattern matching
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

The term syntax (\fref{fig:syntax}) is that of a
type-annotated (\textit{à la} Church) simply typed $λ$-calculus
with let-definitions. Binders in $λ$-abstractions and type definitions
are annotated with both their type and their multiplicity (echoing the
typing context from \fref{sec:typing-contexts}). Multiplicity
abstraction and application are explicit.

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
$p$. But, while in the application rule only the argument is affected
by $p$, in the case rule, not only the scrutinee but also the variable
bindings in the branches are affected by $p$. What it means,
concretely, is that the multiplicity of data is \emph{inherited} by
its elements: if we have an $A⊗B$ with multiplicity $1$, then we have
an $A$ with multiplicity $1$ and a $B$ with multiplicity $1$, and if
we have an $A⊗B$ with multiplicity $ω$ then we have an $A$ with
multiplicity $ω$ and a of $B$ with multiplicity $ω$. Therefore, the
following program, which asserts the existence of projections, is
well-typed (note that, both in |first| and |snd|, the arrow is~---~and
must be~---~unrestricted).
\begin{code}
  data (⊗) a b where
    (,) : a ⊸ b ⊸ a⊗b

  first  :: a⊗b → a
  first (a,b)  = a

  snd  :: a⊗b → b
  snd (a,b)  = b
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

\rn{Need operational intuition here.. if we create the pair as a linear
  object, and then we implicitly convert to unrestricted, and then we
  project... where would the linear->GCd-heap copy happen?
  — [aspiwack] no copy happens implicitly: the promotion principle
  (it is an actual rule in typical presentations of linear logic, but
  not ours since it is part of the application rule and friends)
  states that knowing how to make a linear something is sufficient to
  build an unrestricted same-thing (in a scaled context), this is what
  happens implicitly: you pretend you are building a linear whatever,
  but turns out you were building an unrestricted whatever all along.}

\section{\calc{} dynamics}
\label{sec:dynamics}

We wish to give a dynamic semantics for \calc{} which accounts for the
explicit allocations and de-allocations as seen in the queue
example of \fref{sec:queue-api}. To that effect we follow \citet{launchbury_natural_1993} who
defines a semantics for lazy computation.

\citeauthor{launchbury_natural_1993}'s semantics is a big-step
semantics where variables play the role of pointers to the heap (hence
represent sharing, which is the cornerstone of a lazy semantics). To illustrate
the operational benefits of linearity, we
augment that semantics with a foreign heap and queue
primitives, as discussed in \fref{sec:queue-api}. Any similar linear
\textsc{api} can be supported in the same way.

To account for a foreign heap, we have a single logical heap with
bindings of the form $x :_p A = e$ where $p∈\{1,ω\}$ a multiplicity:
bindings with multiplicity $ω$ represent objects on the regular,
garbage-collected, heap, while bindings with multiplicity $1$
represent objects on a foreign heap, which we call the \emph{linear
  heap}. The ``pure'' language of \fref{sec:statics} is extended with
values, types, and primitives for queues.
% Queues and messages are
% represented as literals\footnote{As such, queues will seem to be
%   copied on the stack, but it is just an artifact of the particular
%   presentation: it does not have a syntax for returning ``pointers''.}
% manipulated by the primitives. For the sake of simplicity of
% presentation, we only show one primitive (\emph{push}) in addition to
% allocation and de-allocation.

\citet{launchbury_natural_1993}'s semantics relies on a constrained
$λ$-calculus syntax which we remind in \fref{fig:launchbury:syntax}, and
extend \citet{launchbury_natural_1993}'s original syntax with
\begin{description}
\item[Message literals] We assume a collection of message literals
  written $m_i$. In a real-world scenario, messages would have some
  structure, but for the purpose of this semantics we consider them as
  simple constants. The type of messages is |Msg|.

\item[Queue values] Queues are represented as values of the form
  $⟨m_{i_1},…,m_{i_n}⟩$ (as a convention, messages are pushed to the
  left, and exit to the right). We assume that such queue values are
  not part of the source program: they are created by primitive
  operations. Therefore queue literals will only be found in
  the heap (and specifically on the linear heap). The type of queues
  is |Queue|.

\item[Primitives] The primitive functions
  $alloc : (Queue ⊸ Bang A) ⊸ Bang A$, $push : Queue ⊸ Queue $ and
  $pop : Queue ⊸ Maybe(Bang Msg,Queue)$ are responsible respectively
  for allocating an empty queue, pushing a message to a queue, and popping a
  message from a queue. The $pop$ primitive also de-allocates its
  argument if it is an empty queue.
\end{description}
\todo{typing rules for alloc, push and free, and literals.}
\todo{in the translation, add rules for the multiplicity abstraction
  and application}

\begin{figure}

  % \figuresection{Syntax of the runtime language}
  % \begin{align*}
  %   r &::=\\
  %     &||  x\\
  %     &||  λx. r\\
  %     &||  r x\\
  %     &||  λπ. r\\
  %     &||  r p\\
  %     &||  c x₁ … x_n\\
  %     &||  \case[q] r {c_k  x₁ … x_{n_k} → r_k}\\
  %     &||  \flet x_1 =_{q₁} r₁ … x_n =_{q_n} r_n \fin r\\
  %     &||  m_i\\
  %     &||  alloc k\\
  %     &||  push y z\\
  %     &||  free x
  % \end{align*}

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

The dynamic semantics is given in \fref{fig:dynamics}. Let us review
the new rules
\begin{description}
\item[Linear variable] In the linear variable rule, the binding in the
  linear heap is removed. While this can be exploited to signify
  explicit de-allocation of objects on the linear heap. However, the
  linear variable rule is best seen as a technical device to represent
  the strictness of the queue primitives: the queue literal will then
  be passed to a primitive, either \emph{free} to actually free the
  queue, or \emph{push} to augment the queue with a message.
\item[Alloc] The alloc rule creates a new (empty) queue and pass it to
  its continuation. It is not the only rule which allocate in the
  sense of using a |malloc|-like primitive: pushing a message to a
  queue may require allocation to accommodate for the extra
  element. However its role is to allocate a root that will own a
  queue.
\item[Push] The push rule adds a message to a queue. Notice that the
  message itself is incorporated into the queue literal: there is no
  mention of a variable pointing to the message. This is because the
  message is copied from the garbage-collected heap to the linear
  heap.
\item[Pop] The $pop$ primitive has two rules: when the queue contains
  messages, the right-most message is returned (as well as a new
  handle to the queue), when the queue is empty, it is
  deallocated. The non-empty case is a little wordy because it must
  ``allocate'' new variables on the heap in order to create a
  $Just(w,y)$ value (to comply to the syntax, $Just$ can only be
  applied to variables).\improvement{[aspiwack] I've cheated a bit,
    here, as I've inlined the pair constructor inside $Just$ which is
    not strictly speaking permitted.}
\end{description}

\begin{figure}
  \begin{mathpar}
    \inferrule{ }{Γ : λπ. t ⇓ Γ : λπ. t}\text{m.abs}


    \inferrule{Γ : e ⇓ Δ : λπ.e' \\ Δ : e'[q/π] ⇓ Θ : z} {Γ :
      e q ⇓_ρ Θ : z} \text{m.app}

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

    \inferrule{Γ,x :_1 Queue = ⟨⟩ : k x ⇓ Δ : z }{Γ: alloc k ⇓ Δ : z }\text{alloc}

    \inferrule{Γ:y ⇓ Δ:⟨…⟩ \\ Δ:w ⇓ Θ:m_i}{Γ : push y w⇓ Θ : ⟨m_i,…⟩}\text{push}

    \inferrule{Γ:x ⇓ Δ:⟨…,m_i⟩ }{Γ : pop x ⇓ Δ,w_0:_ω Msg = m_i, w:_1 Bang w_0, y:_1 Queue = ⟨…⟩ : Just (w,y) }\text{pop$_1$}

    \inferrule{Γ:x ⇓ Δ:⟨⟩ }{Γ : pop x ⇓ Δ : () }\text{pop$_2$}

  \end{mathpar}

  \caption{Dynamic semantics}
  \label{fig:dynamics}
\end{figure}

While the semantics of \fref{fig:dynamics} describes quite closely
what is implemented in the \textsc{ghc} extension prototype, it is not
convenient for proving properties. There are two reasons to that fact:
first the semantics is rather \improvement{weasel word}disjoint from the type system and, also,
there are pointers from the garbage-collected heap to the linear
heap. Such pointers will occur, for instance, if the programmer
needs a pair of queues: the pair will be allocated on the
garbage-collected heap while the queues will live in the linear heap.

This is not a problem in and on itself: pointers to queue may be seen
as opaque by the garbage collector which will not collect them, so
that their lifetime is still managed explicitly by the
programmer. However, in order to prevent use-after-free bug, we must
be sure that by the time a queue is freed, every object in the
garbage-collected heap which points to that queue must be dead, even
if they are still extant in the heap.

In order to prove such a property, let us introduce a stronger
semantics with the lifetime of objects more closely tracked. The
strengthened semantics differs from \fref{fig:dynamics} in two
aspects: the evaluation states are typed, and values with statically
tracked lifetimes (linear values) are put on the linear
heap.

In order to define the typed semantics, we shall introduce a few
notations. First we will need a notion of product annotated with the
multiplicity of its first component.
\begin{definition}[Weighted tensors]

  We use $A~{}_ρ\!⊗ B$ ($ρ∈\{1,ω\}$) to denote one of the two following
  types:
  \begin{itemize}
  \item $\data A~{}_1\!⊗ B = ({}_1\!,) : A ⊸ B ⊸ A~{}_1\!⊗ B$
  \item $\data A~{}_ω\!⊗ B = ({}_ω\!,) : A → B ⊸ A~{}_1\!⊗ B$
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
  for $(e_1 {}_{ρ_1}\!, (…, (e_n{}_{ρ_n},())))$, and
  $\multiplicatedTypes{e_1 :_{ρ_1} A_1, … , e_n :_{ρ_n} A_n}$ for
  $A_1{}_{ρ_1}\!⊗(…(A_n{}_{ρ_n}\!⊗()))$.
\end{definition}

\begin{definition}[Strengthened reduction relation]
  We define the strengthened reduction relation, also written $⇓$, as a
  relation on annotated state. Because $Ξ$, $ρ$, $A$ and $Σ$ will
  always be the same for related states, we abbreviate
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

\inferrule{Ξ ⊢ (Γ,x :_1 Queue = ⟨⟩ || k x ⇓ Δ || z) :_1 Bang A,Σ }{Ξ ⊢
  (Γ || alloc k ⇓ Δ || z) :_ρ Bang A,Σ}\text{alloc}

\inferrule{Ξ ⊢ (Γ||y ⇓ Δ||⟨…⟩) :_1 Queue, w:_ω Msg,Σ\\ Ξ ⊢ (Δ||w ⇓ Θ||m_i) :_1
  Msg,Σ}{Ξ ⊢ (Γ || push y w⇓ Θ || ⟨m_i,…⟩) :_1 Queue,Σ}\text{push}

\inferrule{Ξ ⊢ (Γ||x ⇓ Δ||⟨…⟩) :_1 (),Σ}{Ξ ⊢ (Γ || free x ⇓ Δ || ()) :_1 (),Σ}\text{free}

\inferrule{Ξ ⊢ (Γ||x ⇓ Δ||⟨…,m_i⟩) :_1 Queue,Σ}{Ξ ⊢ (Γ || pop x ⇓
  Δ,w_0:_ω Msg = m_i, w:_1 Bang w_0, y:_1 Queue = ⟨…⟩ || Just (w,y)) :_1 Maybe(Bang Msg,Queue),Σ}\text{pop$_1$}

\inferrule{Ξ ⊢ (Γ||x ⇓ Δ||⟨⟩) :_1 Queue,Sigma}{Ξ ⊢ (Γ || pop x ⇓ Δ || ()) }\text{pop$_2$}

  \end{mathpar}
  \caption{Typed operational semantics. (Omitting the obvious m.abs and m.app for concision)}
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
the form $\varid{Bang} x$ of multiplicity $1$ while returning a
result of multiplicity $ω$. This constraint is crucial, because the |alloc| rule is the
only rule which makes it possible to use of a linear value in order to produce a
garbage collected value, which in turn justifies that in the ordinary
semantics, queues can be allocated in the linear heap. The reason why
it is possible is that, by definition, in $\varid{Bang} x$, $x$ \emph{must} be
in the garbage-collected heap. In other words, when an expression $e :
\varid{Bang} A$ is forced to the form $\varid{Bang} x$, it will have consumed all the
pointers to the linear heap (the correctness of this argument is
proved in \fref{lem:type-safety} below).

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

  \todo{There used to be the case of the case-bang in more details,
    probably do alloc instead}
  % The important case is the case-bang rule. By induction we have that
  % $Ξ,y:_ω⊢(Δ||Bang x) :_1 Bang A,…$. Unfolding the typing rule for
  % $Bang$, we have that $Δ=ωΔ'$ for some $Δ'$. Which is sufficient to
  % prove that $Ξ⊢(Δ||u[x/y]) :_ω C , Σ$.
\end{proof}

Because of this property we can freely consider the restriction of the
strengthened relation to well-typed states. For this reason, from now
on, we only consider well-typed states.

\begin{corollary}[Never stuck on the linear variable rule]\label{cor:linear-variable}
  $Ξ ⊢ (Γ,x:_1A=e ||x) :_ωB , Σ$ is not reachable.
\end{corollary}
\begin{proof}
  Remember that we consider only well-typed states because of
  \fref{lem:type-safety}. Unfolding the typing rules it is easy
  to see that $Ξ ⊢ (Γ,x:_1A=e ||x) :_ωB , Σ$ is not well-typed: it
  would require $x:_1 A = ωΔ$ for some $Δ$, which cannot be.
\end{proof}

We are now ready to prove properties of the ordinary semantics by
transfer of properties of the strengthened semantics. Let us start by
defining a notion of type assignment for states of the ordinary
semantics.

\newcommand{\ta}[2]{γ(#1)(#2)}

\improvement{Explain what $Γ'$ ranges over.}
\begin{definition}[Type assignment]
  A well-typed state is said to be a type assignment for an ordinary
  state, written $\ta{Γ:e}{Ξ ⊢ Γ' || e' :_ρ A , Σ}$, if
  $e=e' ∧ Γ' \leqslant Γ$.

  That is, $Γ'$ is allowed to strengthen some $ω$ bindings to be
  linear, and to drop unnecessary $ω$ bindings.
\end{definition}

Notice that for a closed term, type assigment reduces to the fact that
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

From type-safety follows the fact that a completely evaluated program
has necessarily de-allocated all the linear heap. This is a form of
safety from resource leaks (of course, resource leaks can always be
programmed in, but the language itself does not leak resources).

\begin{corollary}[Eventual de-allocation of linear values]
  Let $⊢ t : ()$ be a closed term, where $\data () = ()$ is the data
  declaration with a single constructor. If $:t ⇓ Δ:()$, then $Δ$ only
  contains $ω$-bindings.
\end{corollary}
\begin{proof}
  By \fref{lem:actual_type_safety},
  we have $⊢ (Δ||() :_ρ ()), ⋅ $. Then the typing rules of $\flet$ and
  $()$ conclude: in order for $()$ to be well typed, the environment
  introduced by $\flet Δ$ must be of the form $ωΔ'$.
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
blocked, in particular that garbage-collected objects which point to the
linear objects are not dereferenced after the linear object has been
freed: \calc{} is safe from use-after-free errors.

\section{Perspectives}
\todo{Speak about fusion}
\hfill\\
\todo{Mention the case-bang rule (the case-bang rule can be found in
  the source below this todo-box)}
\providecommand\casebangrule{\inferrule{Γ: t ⇓_{q} Δ : \varid{Bang} x
    \\ Δ : u[x/y] ⇓_ρ Θ : z} {Γ :
    \mathsf{case}_{q} t \mathsf{of} \{\varid{Bang} y ↦ u\} ⇓_ρ Θ :
    z}\text{case-bang}}
\hfill\\
\todo{More multiplicities}
\hfill\\
\todo{Discussion on negative types and how they are encoded (there are
  not provided natively)}

\section{Related work}

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
in~\citet{bernardy_composable_2015}.\todo{call-back to fusion in the
  perspectives}.

Several points guided our choice of designing \HaskeLL{} around linear
logic rather than uniqueness types: 1. functional languages have more use
for fusion than in-place update (\textsc{ghc} has a cardinality
analysis, but it does not perform a non-aliasing analysis); 2 with modern computer architectures in-place update is no longer crucial for performance (accessing RAM requires making copies anyway); 3. there is a
wealth of literature detailing the applications of linear
logic — explicit memory
management~\cite{lafont_linear_1988,hofmann_in-place_,ahmed_l3_2007},
array
computations~\cite{bernardy_duality_2015,lippmeier_parallel_2016},
protocol specification~\cite{honda_session_1993}, privacy
guarantees\cite{gaboardi_linear_2013}, graphical
interfaces\cite{krishnaswami_gui_2011}; 4. and desicively, linear type systems are
conceptually simpler than uniqueness type systems, which gave a
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
both\footnote{See Edsko de Vries's recent exposition at
  \url{http://edsko.net/2017/01/08/linearity-in-haskell/}}.

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
such compatibility is pretty much necessary to accomodate the dependently-typed kinds of \textsc{ghc}.

\subsection{Alms}
\improvement{Citation pointing to \emph{e.g.}
  \url{http://users.eecs.northwestern.edu/~jesse/pubs/alms/} (And
  rewrite this paragraph which contains a copy-paste of the paper's
  abstract.)}
Alms is an \textsc{ml}-like language based on affine types (a variant
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
Rust, as a programming language, is specifically optimized for writing
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
required, instead of computer $ωΓ$, it is enough to check that
$ρ=ω$. The problem is that this check is arguably too coarse, and
result into the following being derivable:
$$
⊢_ω λx. (x,x) : A ⊸ (A⊗A)
$$
Which we do not consider desirable: it means that there cannot be
reusable definitions of linear functions. In terms of linear logic,
\citeauthor{mcbride_rig_2016} makes the natural arrow $!(A⊸B) ⟹ !A⊸!B$
invertible.

In that respect, our system is closer to
\citeauthor{ghica_bounded_2014}'s. What we keep from
\citeauthor{mcbride_rig_2016}, is the typing rule of |case| (see
\fref{sec:statics}), which can be phrased in terms of linear logic as
making the natural arrow $!A⊗!B ⟹ !(A⊗B)$ invertible. This choice is
unusual from a linear logic perspective, but it is the key to be able
to use types both linearly an unrestrictedly without intrusive
multiplicity polymorphic annotation on all the relevant types.

The literature on so-called coeffects uses type systems similar to
\citeauthor{ghica_bounded_2014}, except with a linear arrow and
multiplicities carried by the exponential modality
instead. \Citet{brunel_coeffect_core_2014}, in particular, develops a
Krivine realisability model for such a calculus. We are not aware of
an account of Krivine realisability for lazy languages, hence it is
not directly applicable to \calc.

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

\section{Conclusion}

This paper demonstrates how an existing lazy language, such
as Haskell, can be extended with linear types, without compromising
the language, in the following sense:
\begin{itemize}
\item Existing programs are valid in the extended language
  \emph{without modification}.
\item Such programs retain the same semantics.
\item Furthermore, the performance of existing programs is not affected.
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
reduce \textsc{gc} pressure and latency, we only need to modify the
type system: primitives to manipulate foreign data can be implemented
in libraries using the foreign function interface. This helps make the
prototype quite lean.

\bibliography{../PaperTools/bibtex/jp.bib,../local.bib}{}
\bibliographystyle{ACM-Reference-Format.bst}

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
%  LocalWords:  unannotated tuple subkinding invertible coeffects
%  LocalWords:  unrestrictedly bidirectionality
