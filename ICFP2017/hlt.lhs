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

%% Deactivated for submission period
%\usepackage[colorinlistoftodos,prependcaption,textsize=tiny]{todonotes}
\setlength{\marginparwidth}{2.5cm} % Here's a size that matches the new PACMPL format -RRN
\usepackage{xargs}
%% Deactivated for submission perdiod
%\newcommandx{\unsure}[2][1=]{\todo[linecolor=red,backgroundcolor=red!25,bordercolor=red,#1]{#2}}
% \newcommandx{\info}[2][1=]{\todo[linecolor=OliveGreen,backgroundcolor=OliveGreen!25,bordercolor=OliveGreen,#1]{#2}}
% \newcommandx{\change}[2][1=]{\todo[linecolor=blue,backgroundcolor=blue!25,bordercolor=blue,#1]{#2}}
% \newcommandx{\inconsistent}[2][1=]{\todo[linecolor=blue,backgroundcolor=blue!25,bordercolor=red,#1]{#2}}
% \newcommandx{\critical}[2][1=]{\todo[linecolor=blue,backgroundcolor=blue!25,bordercolor=red,#1]{#2}}
% \newcommandx{\improvement}[2][1=]{\todo[linecolor=Plum,backgroundcolor=Plum!25,bordercolor=Plum,#1]{#2}}
% \newcommandx{\resolved}[2][1=]{\todo[linecolor=OliveGreen,backgroundcolor=OliveGreen!25,bordercolor=OliveGreen,#1]{#2}} % use this to mark a resolved question
% \newcommandx{\thiswillnotshow}[2][1=]{\todo[disable,#1]{#2}} % will replace \resolved in the final document

% % Peanut gallery comments by Ryan:
% \newcommandx{\rn}[1]{\todo[]{RRN: #1}}
% \newcommandx{\simon}[1]{\todo[]{SPJ: #1}}

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

%% Deactivated for submission period
% For outlining / psuedotext.
% \newcommand{\note}[1]{
%   \textcolor{blue}{
%   \begin{itemize}
%   \item #1
%   \end{itemize}}}

% \newcommand{\Red}[1]{\textcolor{red}{#1}}
% \newcommand{\new}[1]{\textcolor{blue}{#1}}

% Title portion

% Put working title proposals here:
% \title{\HaskeLL}
% \title{\HaskeLL: Linear types with backwards compatibility in an established language}
% \title{\HaskeLL: Linear types with Backwards Compatibility}
% \title{\HaskeLL: Systems Programming with \\ Backwards-Compatible Linear Types}

\title{Retrofitting Linear Types}

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

Can we {\em safely} use Haskell to implement a low-latency server that caches
a large dataset in-memory? Today, the answer is
``no''\cite{pusher_latency_2016},
because pauses incurred by garbage collection (GC), observed in the
order of 50ms or more, are unacceptable. Pauses are in general
proportional to the size of the heap. Even if the GC is incremental,
the pauses are unpredicable, difficult to control by the programmer
and induce furthermore for this particular use case a tax on overall
throughput. The problem is: the GC is not {\em resource efficient},
meaning that resources aren't always freed as soon as they could be.
Programmers can allocate such large,
long-lived data structures in manually-managed off-heap memory,
accessing it through FFI calls. Unfortunately this common technique
poses safety risks: space leaks (by
failure to deallocate at all), as well use-after-free or double-free
errors just like programming in plain C. The programmer has then
bought resource efficiency but at the steep price of giving up on
resource safety.
If the type system was {\em resource-aware}, a programmer wouldn't
have to choose.

It is well known that type systems {\em can} be useful for controlling
resource usage, not just ensuring correctness. Affine types~\cite{tov_practical_2011}, linear
types~\cite{lafont_linear_1988,wakeling_linearity_1991}, permission types~\cite{westbrook_permissions_2012} and capabilities
\cite{chargueraud_functional_2008,balabonski_mezzo_2016} enable
  resource safe as well resource efficient
handling of scarce resources such as
sockets and file handles.  All these approaches have been extensively
studied, \emph{yet these ideas have had relatively little effect on
  programming practice}.  Few practical, full-scale languages are
designed from the start with such features.  Rust is the major
exception~\cite{matsakis_rust_2014}, and in Rust we see one of the
attendant complications: adding advanced resource-tracking features
puts a burden on new users, who need to learn how to satisfy the
``borrow checker''.


We present in this paper the first type system that we believe has
a good chance of influencing existing functional programs and
libraries to become more resource efficient.
%
Whereas in Rust new users and casual programmers have to buy the whole
enchilada, we seek to devise a language that is resource safe always
and resource efficient sometimes, only when and where the programmer
chooses to accept that the extra burden of proof is worth the better
performance. Whereas other languages make resource efficiency {\em
  opt-out}, we seek to make it {\em opt-in}.
%
We do this
by retrofitting a \emph{backward-compatible extension} to
a Haskell-like language. Existing
functions continue to work, although they may now have more refined types
that enable resource efficiency; existing data structures continue to work, and
can additionally track resource usage.  Programmers who do not need
razor sharp resource efficiency
should not be tripped up by it. They need not even know about our type
system extension. We make the following specific contributions:

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
  \cite{wakeling_linearity_1991}.

\item We formalise \HaskeLL{} as \calc{}, a linearly-typed extension of the
  $λ$-calculus with data types (\fref{sec:statics}).
  % (Rust has no such formalism.): of course not; and it's not based on
  % lambda-calculus anyway. Seems like we're running out of arguments,
  % so I remove this.
  We provide its type system,
  highlighting how it is compatible with existing Haskell features,
  including some popular extensions.
  The type system of \calc{} has a number of unusual features, which together support
  backward compatibility with Haskell: linearity appears only in bindings
  and function arrows, rather than pervasively in all types; we support linearity polymorphism
  (\fref{sec:lin-poly}); and the typing rule for $\textsf{case}$ is novel (\fref{sec:typing-rules}).
  No individual aspect is entirely new (\fref{sec:related-type-systems}), but collectively
  they add up to an unintrusive system that can be used in practice and scales up
  to a full programming language implementation with a large type system.

\item We provide a dynamic semantics for \calc{},
  combining laziness with explicit deallocation of linear data (\fref{sec:dynamics}).
  We prove type safety, of course.  But we also prove that the type system guarantees
  the key memory-management properties that we seek: that every
  linear value is eventually deallocated by the programmer, and is never referenced after
  it is deallocated.

\item Type inference, which takes us from the implicitly-typed
  source language, \HaskeLL{}, to the explicitly-typed intermediate
  language \calc{}, is not covered this paper.
  However, we have implemented a proof of concept, by modifying the leading
  Haskell compiler \textsc{ghc} to infer linear types.  The prototype is freely
  available\footnote{URL suppressed for blind review, but available on request}, and
  provides strong evidence that it is not hard to extend
  \textsc{ghc}'s full type inference algorithm as currently
  implemented (despite its complexity) with linear types.
\end{itemize}
Our work is directly motivated by the needs of large-scale low-latency applications in industrial
practice. In \fref{sec:applications} we show how \HaskeLL{} meets those needs.
The literature is dense with related work, which we dicuss in \fref{sec:related}.


\section{A taste of \HaskeLL}
\label{sec:programming-intro}
We begin with an overview of
\HaskeLL, our proposed extension of Haskell with linear types. All informal claims made in this section are substantiated later on.
%
First, along with the usual arrow type |A -> B|,
we propose an additional arrow type, standing for \emph{linear functions}, written
|A ⊸ B|. In the body of a linear function, the type system tracks that
there is exactly one copy of the parameter to consume.
\begin{code}
f :: A ⊸ B       bigSpace bigSpace         bigSpace   g :: A -> B
f x = {- |x| has multiplicity $1$ here -}   bigSpace   g y = {- |y| has multiplicity $\omega$ here -}
\end{code}
\noindent
We say that the \emph{multiplicity} of |x| is $1$ in the body of |f|; and that of |y| is $ω$ in |g|. Similarly, we say
that unrestricted (non-linear) parameters have multiplicity $ω$ (usable
any number of times, including zero). We call
a function \emph{linear} if it has type |A ⊸ B| and \emph{unrestricted} if it has
type |A -> B|.

The linear arrow type |A ⊸ B| guarantees that any function with that type will
consume its argument exactly once.
Note, however, that the type
\emph{places no requirement on the caller} of these functions.
The latter is free to pass either a linear or non-linear value to the function.
%
For example, consider these definitions of a function |g|:
\begin{code}
g1,g2,g3 :: (a ⊸ a -> r) -> a ⊸ a -> r

g1 k x y = k x y          -- Valid
g2 k x y = k y x          -- Invalid: fails |x|'s multiplicity guarantee
g3 k x y = k x (k y y)    -- Valid: |y| can be passed to linear |k|
\end{code}
As in |g2|, a linear variable |x| cannot be passed to the non-linear
function |(k y)|.  But the other way round is fine:
|g3| illustrates that the non-linear variable |y| can be passed
to the linear function |k|. Linearity is a strong contract for the
implementation of a function, not its caller.

\subsection{Calling contexts and promotion}
\label{sec:calling-contexts}

A call to a linear function consumes its argument once only if the
call itself is consumed once.  For example, consider these definitions
of the same function |g|:
\begin{code}
f :: a ⊸ a
g4,g5,g6 :: (a ⊸ a -> r) -> a ⊸ a -> r

g4 k x y = k x (f y)      -- Valid: |y| can be passed to linear |f|
g5 k x y = k (f x) y      -- Valid: |k| consumes |f x|'s result once
g6 k x y = k y (f x)      -- Invalid: fails |x|'s multiplicity guarantee
\end{code}
In |g5|, the linear |x| can be passed to |f| because the result of |(f x)| is
consumed linearly by |k|.  In |g6|, |x| is still passed to the linear function
|f|, but the call |(f x)| is in a non-linear context, so |x| too is
used non-linearly and the code is ill-typed.

In general, any sub-expression is type-checked as if it were to be
consumed exactly once. However, an expression which does not contain
linear resources, that is an expression whose free variables all have
multiplicity $ω$, like |f y| in |g4|, can be consumed many times. Such
an expression is said to be \emph{promoted}. We leave the specifics to
\fref{sec:statics}.

\subsection{Linear data types}
\label{sec:linear-constructors}

Using the new linear arrow, we can (re-)define Haskell's list type as follows:
\begin{code}
data [a] where
  []   :: a
  (:)  :: a ⊸ [a] ⊸ [a]
\end{code}
That is, we give a linear type to the |(:)| data constructor.
Crucially, this is
not a new, linear list type: this \emph{is} \HaskeLL{}'s list type, and all
existing Haskell functions will work over it perfectly well.  But we can
\emph{also} use the very same list type to contain linear resources (such as
file handles) without compromising safety; the type system ensures
that resources in a list will eventually be deallocated, and that they
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

Giving a more precise type to |(++)| only
{\em strengthens} the contract that |(++)| offers to its callers;
\emph{it does not restrict its usage}. For example:
\begin{code}
  sum :: [Int] ⊸ Int
  f :: [Int] ⊸ [Int] -> Int
  f xs ys = sum (xs ++ ys) + sum ys
\end{code}
Here the two arguments to |(++)| have different multiplicities, but
the function |f| guarantees that it will consume |xs| precisely once.

For an existing language, being able to strengthen |(++)|, and similar functions, in a {\em
  backwards-compatible} way is a huge boon.
%
Of course, not all functions are linear: a function may legitimately
demand unrestricted input.
For example, the function |f| above consumed |ys| twice, and so |ys| must
have multiplicity $\omega$, and |f| needs an unrestricted arrow for that argument.

Generalising from lists to arbitrary algebraic data types,
we designed \HaskeLL{} so that when in a traditional Haskell
(non-linear) calling context, linear constructors
degrade to regular Haskell data types. Thus our radical position
is that data types in \HaskeLL{} should have {\em linear fields by default},
including all standard definitions, such as pairs, tuples, |Maybe|, lists, and so on.
More precisely, when defined in old-style Haskell-98 syntax, all fields are
linear; when defined using GADT syntax, the programmer can explicitly choose.
For example, in our system, pairs defined as
\begin{code}
data (,) a b = (,) a b
\end{code}
would use linear arrows. This becomes explicit when defined in GADT syntax:
\begin{code}
data (a,b) where  (,) ::  a ⊸ b ⊸ (a,b)
\end{code}
We will see in \fref{sec:non-linear-constructors} when it is also useful
to have contstructors with unrestricted arrows.

\subsection{Linearity polymorphism}
\label{sec:lin-poly}

As we have seen, implicit conversions between multiplicities make
first-order linear functions {\em more general}. But the higher-order
case thickens the plot. Consider that the standard |map| function over
(linear) lists:
\begin{code}
map f []      = []
map f (x:xs)  = f x : map f xs
\end{code}
It can be given the two following incomparable types:
  |(a ⊸ b) -> [a] ⊸ [b]|  and
  |(a -> b) -> [a] -> [b]|.
%
Thus, \HaskeLL{} features quantification over multiplicities and parameterised arrows (|A → _ q B|).
Using these, |map| can be given the following most general type:
|∀ρ. (a -> _ ρ b) -> [a] -> _ ρ [b]|.
%
Likewise, function composition can be given the following general type:
\begin{code}
(∘) :: forall π ρ. (b → _ π c) ⊸ (a → _ ρ b) → _ π a → _ (ρ π) c
(f ∘ g) x = f (g x)
\end{code}
That is: two functions that accept arguments of arbitrary
multiplicities ($ρ$ and $π$ respectively) can be composed to form a
function accepting arguments of multiplicity $ρπ$ (\emph{i.e.} the
product of $ρ$ and $π$ --- see \fref{def:equiv-multiplicity}).
%
Finally, from a backwards-compatibility perspective, all of these
subscripts and binders for multiplicity polymorphism can be {\em
  ignored}. Indeed, in a context where client code does not use
linearity, all inputs will have multiplicity $ω$, and transitively all
expressions can be promoted to $ω$. Thus in such a context the
compiler, or indeed documentation tools, can even altogether hide
linearity annotations from the programmer when this language
extension is not turned on.

\subsection{Operational intuitions}
\label{sec:consumed}

Suppose that a linear function takes as its argument a {\em resource},
such as a file handle, channel, or memory block.  Then the function guarantees:
\begin{itemize}
\item that the resource will be consumed by the time it
  returns;
\item that the resource can only be consumed once; so it will never be
  used after being destroyed.
\end{itemize}
In this way, the linear type system of \HaskeLL{} ensures both that
resource deallocation happens, and that no use-after-free error
occurs.

But wait! We said earlier that a non-linear value can be passed to a linear
function, so it would absolutely \emph{not} be safe for the function to always deallocate its
argument when it is consumed!  To understand this we need to explain our operational model.
%
In our model there there are two heaps: the familiar
\emph{dynamic heap} managed by the garbage collector, and a \emph{linear heap}
managed by the programmer supported by statically-checked guarantees.
Assume for a moment two primitives to allocate and free objects on the linear heap:
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
contain (point to) linear values (but the converse is possible). This
makes sense: after all, if the GC deallocates a value in the dynamic
heap that points off-heap, then the off-heap data will be left
dangling (being off-heap, the GC cannot touch it) with no means to free
it manually. Conversely, a pointer from a resource to the heap can
simply act as a new programmer-controlled GC root. We prove this
invariant in \fref{sec:dynamics}.

We have said repeatedly that ``a linear function guarantees
to consume its argument exactly once if the call is consumed
exactly once''. But what does \emph{``consume exactly once''} mean?
We can now give a more precise operational intution:
a value is said to be consumed if it
either returned, passed to a (linear) function (or constructor) whose
result is itself consumed, or consumed by forcing it:
\begin{itemize}
\item To consume exactly once a value of an atomic base type, like |Int| or |Ptr|, just evaluate it.
\item To consume a function exactly once, call it, and consume its result exactly once.
\item To consume a pair exactly once, evaluate it and consume each of its components excatly once.
\item More generally, to consume exactly once a value of an algebraic data type, evaluate
  it and consume all its linear components exactly once.
\end{itemize}

\subsection{Linearity of constructors: the usefulness of unrestricted constructors}
\label{sec:non-linear-constructors}

We saw in \fref{sec:linear-constructors} that data types in \HaskeLL{} have
linear arguments by default. Do we ever need data constructors
unrestricted arguments?  Yes, we do.

Using the type |T| of \fref{sec:consumed}, suppose we wanted a primitive
to copy a |T| from the linear heap to the dynamic heap. We could define it
in CPS style but a direct style is more convenient:
\begin{code}
  copyT :: (T -> r) ⊸ T ⊸ r bigSpace vs. bigSpace copyT :: T ⊸ Unrestricted a
\end{code}
where |Unrestricted| is a data type with
a non-linear constructor\footnote{The type constructor
  |Unrestricted| is in fact an encoding of the so-called \emph{exponential}
  modality written ${!}$ in linear logic.}:
\begin{code}
  data Unrestricted a where Unrestricted :: a → Unrestricted a
\end{code}
The |Unrestricted|
data type is used to indicate that when a value |(Unrestricted x)| is consumed
once (see \fref{sec:consumed}) we have no guarantee about how often |x| is
consumed.
With our primitive in hand, we can now use ordinary code to copy
a linear list of |T| values into the dynamic heap (we mark patterns with |!| as a reminder that \HaskeLL{}
does not support lazy pattern bindings for linear values):
\begin{code}
  copy :: (a ⊸ Unrestricted a) -> [a] ⊸ Unrestricted [a]
  copy copyElt (x:xs) = Unrestricted (x':xs')  where  !(Unrestricted xs')  = copy xs
                                                      !(Unrestricted x')   = copyElt x
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

Imagine
a server application which receives data and then
stores it for a while before sending it out to receivers, perhaps in
a different order. This general pattern characterizes a large class of
low-latency servers of in-memory data, such as
Memcached~\cite{memcached} or burst
buffers~\cite{liu_burstbuffer_2012}.

As an example, consider a software packet switch. First, we
need to read packets from, and send them to network interfaces.
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
The mailbox handle must be eventually passed to |close| in order to
release it.
%
For each mailbox, the next available packet is yielded by |get|, whereas |send| forwards packet on the
network.
\begin{code}
  get   :: MB ⊸ (Packet , MB)
  send  :: Packet ⊸ ()
\end{code}
%
In the simplest case, we can read a message and send it
immediately~—~without any filtering or buffering.  When calling |get|
and |send|, |Packet|s never need to be copied: they can be passed
along from the network interface card to the mailbox and then to the
linear calling context of |send|, all by reference.

The above API assumes that mailboxes are independent: the order of
packets is ensured within a mailbox queue, but not accross mailboxes
(and not even between the input and output queue of a given
mailbox). While this assumption is in general incorrect, it applies
for our packet switch. Additionally it illustrates the ability of
our type system to finely track dependencies between various kinds of
effects: as precisely as required, but no more.

\paragraph{Buffering data in memory}

So what can our server do with the packets once they are retrieved
from the network? To support software-defined switch policies that
dictate what packet to forward when, we introduce a priority queue.
\begin{code}
data PQ a
empty   :: PQ a
insert  :: Int -> a ⊸ PQ a ⊸ PQ a
next    :: PQ a ⊸ Maybe (a, PQ a)
\end{code}
The interface is familiar, except that since the priority queue must
store packets it must have linear arrows. In this way, the type
system \emph{guarantees} that despite being stored in a data
structure, every packet is eventually sent.

In a packet switch, priorities could represent deadlines associated to
each packet\footnote{whereas in a caching application, the server may
  be trying to evict the bigger packets first in order to leave more
  room for incoming packets}. So we give ourselves a function to infer
a priority for a packet:
\begin{code}
  priority :: Packet ⊸ (Unrestricted Int,Packet)
\end{code}

The take-home message is that the priority queue can be implemented as
a \HaskeLL{} data type. Here is a naive implementation as a sorted
list:
\begin{code}
  data PQ a where
    Empty :: PQ a
    Cons :: Int -> a ⊸ PQ a ⊸ PQ a

  empty = Empty

  insert p x q Empty = Cons p x q
  insert p x (Cons p' x' q')  | p < p'     = Cons p x (Cons p' x' q')
                              | otherwise  = Cons p' x' (insert p x q')

  next Empty = Nothing
  next (Cons __ x q) = Just (x,q)
\end{code}
%
In \fref{sec:lower-gc}, we return to the implementation of the
priority queue and discuss the implications for garbage collection
overheads.

Finally, here is a tiny packet switch that forwards all packets
on the network once three packets are available.
\begin{code}
  sendAll :: PQ Packet ⊸ ()
  sendAll q | Just (p,q')  <- next q = case send p of () -> sendAll q'
  sendAll q | Nothing      <- next q = ()

  enqueue :: MB ⊸ PQ a ⊸ (PQ a,MB)
  enqueue mb q =  let  !(p,mb')                    = get mb
                       !(!(Unrestricted prio),p')  = priority p
                  in ( mb' , insert prio p' q )

  main :: IO ()
  main = withMailbox $ \ mb0 ->  let  !(mb1,q1)  = enqueue mb0 empty
                                      !(mb2,q2)  = enqueue mb1 q1
                                      !(mb3,q3)  = enqueue mb2 q2
                                      !()        = close mb3
                                 in return $ sendAll q3
\end{code}
Note that the various packets \emph{do not have nested lifetimes}, which
rules out region-based approaches. The ability to deal with de-allocation
in a different order to allocation, which ican be very important in practice,
is a crucial feature of approaches based on linear types.
%
\section{\calc{} statics}
\label{sec:statics}
In this section we turn to the calculus at the core of \HaskeLL{},
which we refer to as
\calc{}, and for which we provide a step-by-step account of its syntax and typing
rules.

As we discussed in \fref{sec:consumed}, our operational model for
\calc{} is that of two heaps: the dynamic heap and the linear
heap. Values in the linear heap are managed by the programmer, hence \emph{must} be consumed \emph{exactly
  once}, while values in the dynamic heap are managed by the garbage
collector hence \emph{may} freely be consumed any number of times
(including just once or none at all). The role of the type system of
\calc{} is to enforce this very property.

Let us point out that closures (partial applications or lazy thunks)
may reside in the linear heap. Indeed, as we explained in
\fref{sec:consumed}, values from the dynamic heap do not point to
values in the linear heap, so if any member of a closure resides in
the linear heap, so must the closure itself.

\subsection{Syntax}
\label{sec:syntax}

The term syntax (\fref{fig:syntax}) is that of a type-annotated
(\emph{à la} Church) simply typed $λ$-calculus with let-definitions.
Binders in $λ$-abstractions and type definitions are annotated both
with their type and their multiplicity. Multiplicity abstraction and
application are explicit.

In our static semantics for \calc{} the familiar judgement \(Γ ⊢ t :
A\) has a non-standard reading: it asserts that consuming the term
$t : A$ \emph{exactly once} will consume $Γ$ exactly once
(see \fref{sec:consumed}).

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
            & ||  t s & \text{application} \\
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
generalisation of the intuitionistic arrow and the linear arrow. We
use the following notations:
\(A → B ≝  A →_ω B\) and
\(A ⊸ B ≝ A →_1 B\).

The intuition behind the multiplicity-annotated arrow \(A →_q B\) is
that consuming $f u : B$ exactly once will consume  $q$
times $u{:}A$. Therefore, a function of type $A→B$ \emph{must} be applied to
an argument residing in the dynamic heap, while a function of type
$A⊸B$ \emph{may} be applied to an argument residing on either heap.
%
One might, thus, expect the type $A⊸B$ to be a subtype of $A→B$. This
is however, not so, because there is no notion of subtyping in \calc{}. This
is a salient choice in our design. Our objective is to integrate with
existing typed functional languages such as Haskell and the
\textsc{ml} family, which are based on Hindley-Milner-style
polymorphism. Hindley-Milner-style polymorphism, however, happens not
mesh well with subtyping as the extensive exposition by
\citet{pottier_subtyping_1998} witnesses.  Therefore \calc{} uses
multiplicity polymorphism for the purpose of reuse of higher-order
function as we described in \fref{sec:lin-poly}.

Data type declarations (see \fref{fig:syntax}) are of the following form:
\begin{align*}
  \data D  \mathsf{where} \left(c_k : A₁ →_{q₁} ⋯    A_{n_k} →_{q_{n_k}} D\right)^m_{k=1}
\end{align*}
The above declaration means that \(D\) has \(m\) constructors
\(c_k\) (where \(k ∈ 1…m\)), each with \(n_k\) arguments. Arguments of
constructors have a multiplicity, just like arguments of functions:
an argument of multiplicity $ω$ means that the data type can store,
at that position, data which \emph{must} reside in the dynamic heap;
while a multiplicity of $1$ means that data at that position
\emph{can} reside in either heap. A further requirement is
that the multiplicities $q_i$ must be concrete (\emph{i.e.} either
$1$ or $ω$).

For most purposes, $c_k$ behaves like a constant with the type
$A₁ →_{q₁} ⋯ A_{n_k} →_{q_{n_k}} D$. As the typing rules of
\fref{fig:typing} make clear, this means in particular that from a
value $d$ of type $D$ with multiplicity $ω$, pattern matching
extracts the elements of $d$ with multiplicity $ω$. Conversely, if all
the arguments of $c_k$ have multiplicity $ω$, $c_k$ constructs $D$
with multiplicity $ω$.

Note that, as discussed in \fref{sec:linear-constructors},
constructors with arguments of multiplicity $1$ are not more general
than constructors with arguments of multiplicity $ω$, because if, when
constructing $c u$ with the argument of $c$ of multiplicity $1$, $u$
\emph{may} be either of multiplicity $1$ or of multiplicity $ω$;
dually when pattern-matching on $c x$, $x$ \emph{must} be of
multiplicity $1$ (if the argument of $c$ had been of multiplicity $ω$,
on the other hand, then $x$ could be used either as having
multiplicity $ω$ or $1$).

%%% typing rule macros %%%
\newcommand{\apprule}{\inferrule{Γ ⊢ t :  A →_q B  \\   Δ ⊢ u : A}{Γ+qΔ ⊢ t u  :  B}\text{app}}
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
Many of the typing rules scale contexts by a multiplicity, or add
contexts together. We will
explain the why very soon in \fref{sec:typing-rules}, but first, let
us focus on the how.

In \calc{}, each variable binding, in a typing context, is annotated with a
multiplicity. These multiplicity annotations are the natural counterpart
of the multiplicity annotation on abstractions and arrows.

For multiplicities we need the concrete multiplicities $1$ and $ω$ as
well as multiplicity variables (ranged over by the metasyntactic
variables \(π\) and \(ρ\)) for the sake of polymorphism. However, we
are going to need to add and multiply multiplicities together,
therefore we also need formal sums and products of multiplicities.
%
Multiplicity expressions are quotiented by the following equivalence
relation:
\begin{definition}[equivalence of multiplicities]
  \label{def:equiv-multiplicity}
  The equivalence of multiplicities is the smallest transitive and
  reflexive relation, which obeys the following laws:
\begin{itemize}
\item $+$ and $·$ are associative and commutative
\item $1$ is the unit of $·$
\item $·$ distributes over $+$
\item $ω · ω = ω$
\item $1 + 1 = 1 + ω = ω + ω = ω$
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
    Γ + Δ &= Δ + Γ &
    p (Γ+Δ) &= p Γ + p Δ\\
    (p+q) Γ &= p Γ+ q Γ \\
    (pq) Γ &= p (q Γ) &
    1 Γ &= Γ
  \end{align*}
\end{lemma}

\subsection{Typing rules}
\label{sec:typing-rules}

We are now ready to understand the typing rules of
\fref{fig:typing}. Remember that the typing judgement \(Γ ⊢ t : A\)
reads as: consuming the term $t:A$ once consumes $Γ$ once. But what if
we want to consume $t$ more than once? This is where context scaling
comes into play, like in the application rule:
$$\apprule$$
The idea is that consuming $u$ an arbitrary number of times also
consumes $Δ$ an arbitrary number of times, or equivalently, consumes
$ωΔ$ exactly once. We call this the \emph{promotion
  principle}\footnote{The name \emph{promotion principle} is a
  reference to the promotion rule of linear logic. In \calc{},
  however, promotion is implicit.}: to know how to consume a value any
number of times it is sufficient (and, in fact, necessary) to know how
to consume said value exact once.

To get a better grasp of the application rule and the promotion
principle, you may want to consider how it indeed validates
following judgement. In this judgement, $π$ is a
multiplicity variable; that is, the judgement is
multiplicity-polymorphic:
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
(provided unannotated bindings are understood
as having multiplicity $ω$).
%
The variable rule, as used above, may require some
clarification:
$$\varrule$$
The variable rule implements weakening of
unrestricted variables: that is, it lets us ignore variables with
multiplicity $ω$\footnote{Pushing weakening to the variable rule is
  classic in many $λ$-calculi, and in the case of linear logic,
  dates back at least to Andreoli's work on
  focusing~\cite{andreoli_logic_1992}.}. Note that the judgement
$x :_ω A ⊢ x : A$ is an instance of the variable rule, because
$(x :_ω A)+(x :_1 A) = x:_ω A$. The constructor rule has a similar
$ωΓ$ context: it is necessary to support weakening at the level of
constant constructors.

Most of the other typing rules are straightforward, but let us linger
for a moment on the unusual, yet central to our design, case rule, and specifically on its multiplicity
annotation:
$$\caserule$$
The interesting case is when $p=ω$, which reads as: if we can consume
$t$ an arbitrary number of time, then so can we of its
constituents. Or, in terms of heaps: if $t$ is on the dynamic heap, so
are its constituents (see \ref{sec:consumed}). As a consequence, the
following program, which asserts the existence of projections, is
well-typed (note that, both in |first| and |snd|, the arrow is~---~and
must be~---~unrestricted).
\begin{code}
  first  ::  (a,b) →   a     bigSpace    snd  ::  (a,b) →   b
  first      (a,b)  =  a                 snd      (a,b)  =  b
\end{code}

This particular formulation of the case rule is not implied by the
rest of the system: only the case $p=1$ is actually necessary. Yet,
providing the case $p=ω$
is a design choice which makes it possible to consider data-type
constructors as linear by default, while preserving the semantics of
the intuitionistic $λ$-calculus (as we already stated in
\fref{sec:linear-constructors}). For \HaskeLL{}, it means that types
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

The above technique gives a pure interface to \textsc{i/o}. However, it leaves the possibility
for the programmer to access and old version of the world, as well as the current
one, which is expensive to implement. In practice, one does not want to perform such a duplication,
and thus Haskell solves the issue by forcing the
programmer to use |IO| via its monadic interface.

Linear typing gives a much more direct solution to the problem: if the
|World| is kept linear, then there is no way to observe two different
|World|s. Namely, it is enough to define |IO| as
\begin{align*}
  \data &\varid{IO}_0 a \where \varid{IO}_0 : \varid{World} ⊸ a → \varid{IO}_0 a\\
        &\varid{IO} a = \varid{World} ⊸ \varid{IO}_0 a
\end{align*}
Notice that the $a$ of $\varid{IO} a$ is always unrestricted, so that |IO| has
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
is to obtain a packet, it is sufficient for this section to
consider all the packets. Because there are several mailboxes and each
can get their own streams of packets, we suppose implicitly a
given collection of packets $(p^j_i)_{j,i∈ℕ}$. Where the packet
$p^j_i$ represents the $i$-th package which will be received by the
$j$-th mailbox.

Instead of using the world token as a proxy for an abstract world, we
are using it to keep track of how many mailboxes have been
opened. So the (unique) world token in the stack holds this number.
Similarly, the mailbox tokens are pairs $⟨j,i⟩$ of
integers where $j$ is the mailbox number and $i$ the number of packets
the mailbox has received. In effect, the world and mailbox tokens are
pointers into the infinite matrix of potential packets. We define
these constants as having the same typing rules as zero-ary constructors
(but without the pattern-matching rule):
\emph{e.g.}:
$$
\inferrule{ }{ωΓ ⊢ j : \varid{World}}\text{world}
$$

In addition to the abstract types $\varid{World}$, $\varid{Packet}$ and $\varid{MB}$, and the
concrete types $IO_0$, $IO$, $(,)$, and $()$, \calc{} is extended with
three primitives (see also \fref{sec:packet}):
\begin{itemize}
\item $withMailbox : (\varid{MB} ⊸ \varid{IO} a) ⊸ \varid{IO} a$
\item $close : \varid{MB} ⊸ ()$
\item $get : \varid{MB} ⊸ (\varid{Packet} , \varid{MB})$
\item $send : \varid{Packet} ⊸ ()$
\end{itemize}
Packets $p^j_i$ are considered as constants. We do not model
packet priorities in the semantics, for concision.

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

\begin{figure}
  \figuresection{Translation of typed terms}
  \begin{align*}
    (λ(x:_qA). t)^* &= λ(x:_qA). (t)^* \\
    x^*             &= x \\
    (t  x )^*     &= (t)^*  x \\
    (t  u )^*     &= \flet y :_q A = (u)^* \fin (t)^*  y &
    \text{with $Γ⊢ t : A →_q B$}
  \end{align*}
  \begin{align*}
    c_k  t₁ … t_n   &= \flet x₁ :_{q_1} A_1 = (t₁)^*,…, x_n :_{q_n} A_n = (t_n)^*
                      \fin c_k x₁ … x_n & \text{with $c_k : A_1
                                          →_{q_1}…A_n →_{q_n}D$}
  \end{align*}
  \begin{align*}
    (\case[p] t {c_k  x₁ … x_{n_k} → u_k})^* &= \case[p] {(t)^*} {c_k  x₁ … x_{n_k} → (u_k)^*} \\
    (\flet x_1:_{q₁}A_1= t₁  …  x_n :_{q_n}A_n = t_n \fin u)^* & = \flet x₁:_{q₁}A_1 = (t₁)^*,…, x_n :_{q_n}A_n=_{q_n} (t_n)^* \fin (u)^*
  \end{align*}

  \caption{Syntax for the Launchbury-style semantics}
  \label{fig:launchbury:syntax}
\end{figure}

The dynamic semantics is given in \fref{fig:dynamics}. Let us review
the new rules:
\begin{description}
\item[Linear variable] In the linear variable rule, the binding in the
  linear heap is removed. In conjunction with the rule for $send$, it
  represents deallocation of packets.
\item[WithMailbox] A new $\varid{MB}$ is created with a fresh name $j$. Because it
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
\item[Close] The $close$ primitive consumes the mailbox. Like $send$,
  for the purpose of this semantics, $close$ simply frees the mailbox.
\end{description}

\subsection{Type safety}

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

    \inferrule{Γ:x ⇓ Δ:⟨j,i⟩}{Γ:close x ⇓ Δ:()}\text{close}

    \inferrule
      {Γ:x ⇓ Δ:⟨j,i⟩}
      {Γ:get x ⇓ Δ,x:_1 \varid{MB} = ⟨j,i+1⟩, y:_1 \varid{Packet} = p^j_i : (y,z)}\text{get}

      \inferrule{Γ:x ⇓ Δ:p^j_i}{Γ:send x ⇓ Δ:()}\text{send}
  \end{mathpar}

  \caption{Dynamic semantics}
  \label{fig:dynamics}
\end{figure}

While the semantics of \fref{fig:dynamics} describes quite closely
our plans for implementation in \textsc{ghc}, it is not
convenient for proving properties. There are two reasons to that fact:
first the semantics follows a different structure than the type system and, also,
there are pointers from the garbage-collected heap to the linear
heap. Such pointers occur, for instance, in the priority queue from
\fref{sec:packet}: the queue itself is allocated on the garbage
collected heap while packets are kept in the linear heap.

This is not a problem in and on itself: pointers to packets may be seen
as opaque by the garbage collector, which does not collect them, so
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

In order to define the strengthened semantics, we introduce a few
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
  {Ξ ⊢ (Γ||get x ⇓ Δ,x:_1 \varid{MB} = ⟨j,i+1⟩, y:_1 \varid{Packet} = p^j_i || (y,z)) :_1 (\varid{Packet},\varid{MB}),Σ}\text{get}

\inferrule
  {Ξ ⊢ (Γ||x ⇓ Δ||⟨j,i⟩) :_1 \varid{MB},Σ}
  {Ξ ⊢ (Γ||close x ⇓ Δ||()) :_1 (),Σ}\text{close}

\inferrule
  {Ξ ⊢ (Γ||x ⇓ Δ||p^j_i) :_1 \varid{Packet},Σ}
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
requires $ρ$ to be $1$ (Corollary~\ref{cor:linear-variable} proves
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
%
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
blocked, in particular that garbage-collected objects which point to the
linear objects are not dereferenced after the linear object has been
freed: \calc{} is safe from use-after-free errors.

\section{Applications}
\label{sec:applications}

There is a wealth of literature regarding the application of linear typing to
many practical problems, for instance: explicit memory
management~\cite{lafont_linear_1988,hofmann_in-place_2000,ahmed_l3_2007},
array
computations~\cite{bernardy_duality_2015,lippmeier_parallel_2016},
protocol specification~\cite{honda_session_1993}, privacy
guarantees~\cite{gaboardi_linear_2013} and graphical
interfaces~\cite{krishnaswami_gui_2011}.

This section develops a few examples which are directly usable in
\HaskeLL{}, that is simply by changing Haskell's type system, and
using the dynamic semantics of \fref{sec:dynamics} to justify the
memory safety of a foreign heap implemented using a foreign function
interface.


\subsection{Lowering the \textsc{gc} pressure}
\label{sec:lower-gc}

In a practical implementation of the zero-copy packet example of
\fref{sec:packet}, the priority queue can easily become a bottleneck,
because it will frequently stay large~\cite{pusher_latency_2016}. We can start by having a less
obnoxiously naive implementation of queues, but this optimisation would not solve
the issue which we are concerned with in this section: garbage
collection latency. Indeed, the variance in latency incurred by
\textsc{gc} pauses can be very costly in a distributed application. Indeed,
having a large number of processes which may decide to run a long
pause increases the probability that at least one is running a pause.
Consequently, waiting on a large number of processes is slowed down (by the
slowest of them) much more often than a sequential application. This
phenomenon is known as Little's law~\cite{little_proof_1961}.

A radical solution to this problem, yet one that is effectively used
in practice, is to allocate the priority queue with
|malloc| instead of using the garbage collector's
allocator~\cite[Section IV.C]{marcu_flink_2016}. Our own benchmarks
indicate that peak latencies encountered with large data-structures
kept in \textsc{ghc}'s \textsc{gc} heap are two orders of magnitude
higher than using foreign function binding to an identical
data-structure allocated with |malloc|; furthermore the latency
distribution of \textsc{gc} latency consistently degrades with the
size of the heap, while |malloc| has a much less flat distribution. Of
course, using |malloc| leaves memory safety in the hand of the
programmer.

Fortunately, it turns out that the same arguments that we use
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
promoted (|IO| actions are never promoted because of their |World| parameter),
hence one must make sure that the linear heap is properly emptied,
which is in fact implied by the typing rules for |Unrestricted|.

\subsection{Safe streaming}

The standard for writing streaming applications (\emph{e.g.} reading
from a file) in Haskell is to use a combinator library such as Conduits~\cite{snoyman_conduit_2015}
or Machines~\cite{kmett_machines_2015}. Such libraries have many advantages: they are fast, they
release resources promptly, and they are safe.

However, they come at a significant cost: they are rather difficult to
use. As a result we have observed industrial users walking back from this
type of library to use the simpler, but unsafe Streaming~\cite{thompson_streaming_2015} library.
%
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

\Citet{honda_session_1993} introduces the idea of using types to
represent and enforce protocols. \Citet{wadler_propositions_2012}
showed that \citeauthor{honda_session_1993}'s system is isomorphic to
(classical) linear logic. The high-level idea is that one end of
a communication channel is typed with the protocol $P$ and the other
end with the dual protocol $P^⊥$; for instance: if $A$ denotes ``I expect
an A'', the dual $A^⊥$ denotes ``I shall send an A''. Then, protocols can
be composed using pairs: the protocol $(A,B^⊥)$ means ``I expect an
$A$, and I shall send a $B$''.

In our intuitionistic setting, we can represent the dual $P^⊥$ by using
continuation passing style: $P^⊥ = P⊸⊥$, where $⊥$ represents a type
of effects (|⊥ = IO ()| would be a typical choice in Haskell). This encoding
is the standard embedding of classical (linear) logic in intuitionistic
(linear) logic. Using $P^⊥ = P→⊥$ would not be
sufficient to enforce the protocol $P$, because a process can skip sending a
required value or expect two values where one ought to be sent, potentially causing
deadlocks.

Thus there are two reasons why \calc{} does not have a built-in additive
product ($A\&B$), dual to (linear) sum: 1. uniformity commands to
use the general dualisation pattern instead and 2. the definition would depend on the
choice of effects. The following example (a linear |if|
combinator) shows a glimpse of linear \textsc{cps} code:
\begin{code}
  data A⊕B  = Left :: A ⊸ A⊕B | Right :: B ⊸ A⊕B
  type A&B  = ((A⊸⊥)⊕(B⊸⊥))⊸⊥

if' :: Bool ⊸ (a & a) ⊸ (a ⊸ ⊥) ⊸ ⊥
if' True   p k = p (Left   k)
if' False  p k = p (Right  k)
\end{code}

\section{Related work} \label{sec:related}

\subsection{Regions}

Haskell's |ST| monad~\cite{launchbury_st_1995} taught us
a conceptually simple approach to lifetimes. The |ST| monad has
a phantom type parameter |s| that is instantiated once at the
beginning of the computation by a |runST| function of type:
\begin{code}
  runST :: (forall s. ST s a) -> a
\end{code}
In this way, resources that are allocated during the computation, such
as mutable cell references, cannot escape the dynamic scope of the call
to |runST| because they are themselves tagged with the same phantom
type parameter.

This apparent simplicity (one only needs rank-2 polymorphism)
comes at the cost of strong limitations in practice:
\begin{itemize}
\item |ST|-like regions confine to a stack-like allocation discipline.
  Scopes cannot intersect arbitrarily, limiting the applicability of
  this technique. In our running example, if unused mailboxes have to
  be kept until all mailboxes opened in their scope have been closed, they
  would be hoarding precious resources (like file descriptors).
\item \citet{kiselyov_regions_2008} show that it is possible to
  promote resources in parent regions to resources in a subregion. But
  this is an explicit and monadic operation, forcing an unnatural
  imperative style of programming where order of evaluation is
  explicit. Moreover, computations cannot live directly in |IO|, but
  instead in a wrapper monad. The HaskellR
  project~\cite{boespflug_project_2014} uses monadic regions in the
  style of \citeauthor{kiselyov_regions_2008} to safely synchronise
  values shared between two different garbage collectors for two
  different languages. \Citeauthor{boespflug_project_2014} report that custom monads make
  writing code at an interactive prompt difficult, compromises code
  reuse, force otherwise pure functions to be written monadically and
  rule out useful syntactic facilities like view patterns. In
  contrast, with linear types, values in two regions (in our running
  example packets from different mailboxes) have the same type hence
  can safely be mixed: any data structure containing packet of
  a mailbox will be forced to be consumed before the mailbox is
  closed.
\end{itemize}

\subsection{Finalisers}

A garbage collector can be relied on for more than just cleaning up no
longer extant memory. By registering finalizers (|IO| callbacks) with
values, such as a file handle, one can make it the job of the garbage
collector to make sure the file handle is eventually closed. But
``eventually'' can mean a very long time. File descriptors and other
system resources are particularly scarce: operating systems typically
only allow a small number of descriptors to be open at any one time.
\citet{kiselyov_iteratees_2012} argues that such system resources are
too scarce for eventual deallocation. Prompt deallocation is key.

\subsection{Uniqueness types}

The literature is awash with enforcing linearity not via linear types,
but via uniqueness (or ownership) types. The most prominent representatives of
languages with such uniqueness types are perhaps Clean~\cite{barendsen_uniqueness_1993} and
Rust~\cite{matsakis_rust_2014}. \HaskeLL, on the other hand, is
designed around linear types based on linear
logic~\cite{girard_linear_1987}.

Linear types and uniqueness types are, at their core, dual: whereas a linear type is
a contract that a function uses its argument exactly once
even if the call's context can share a linear argument as many times as it
pleases, a uniqueness type ensures that the argument of a function is
not used anywhere else in the expressions context even if the function
can work with the argument as it pleases.

From a compiler's perspective, uniqueness type provide a {\em non-aliasing
analysis} while linear types provides a {\em cardinality analysis}. The
former aims at in-place updates and related optimisations, the latter
at inlining and fusion. Rust and Clean largely explore the
consequences of uniqueness on in-place update; an in-depth exploration
of linear types in relation with fusion can be found
in~\citet{bernardy_composable_2015}, see also the discussion in
\fref{sec:fusion}.

Because of this weak duality, we perhaps could as well have
retrofitted uniqueness types to Haskell. But several points
guided our choice of designing \HaskeLL{} around linear
logic rather than uniqueness types: (a) functional languages have more use
for fusion than in-place update (if the fact that \textsc{ghc} has a cardinality
analysis but no non-aliasing analysis is any indication); (b) there is a
wealth of literature detailing the applications of linear
logic — see \fref{sec:applications}; (c) and desicively, linear type systems are
conceptually simpler than uniqueness type systems, giving a
clearer path to implementation in \textsc{ghc}.

\subsection{Linearity as a property of types vs. a property of bindings}

In several presentations \cite{wadler_linear_1990,mazurak_lightweight_2010,morris_best_2016}
programming languages incorporate
linearity by dividing types into two kinds. A type is either linear
or unrestricted.

In effect, this distinction imposes a clean separation between the linear world
and the unrestricted world. An advantage of this approach is that it
instantiates both to linear types and to uniqueness types depending on
how they the two worlds relate, and even have characteristics of
both~\cite{devries_linearity_2017}.

Such approaches have been very successful for theory: see for instance
the line of work on so-called \emph{mixed linear and non-linear logic}
(usually abbreviated \textsc{lnl}) started by
\citet{benton_mixed_1995}. However, for practical language design,
code duplication between the linear an unrestricted worlds quickly
becomes costly. So language designers try to create languages with some
kind of kind polymorphism to overcome this limitation. This usually
involves a subkinding relation and bounded polymorphism, and these kind
polymorphic designs are complex. See \citet{morris_best_2016}
for a recent example. We argue
that by contrast, the type system of \calc{} is simpler.

The complexity introduced by kind polymorphism and subtyping relations
makes retrofitting a rich core language such as \textsc{ghc}'s an
arduous endeavour. \textsc{ghc} already supports impredicative
dependent types and a wealth of unboxed or otherwise primitive types
that cannot be substituted for polymorphic type arguments. It is not
clear how to support linearity in \textsc{ghc} by extending its kind system.
In contrast, our design inherits many features of \citeauthor{mcbride_rig_2016}'s,
including its compatibility with dependent types, and
such compatibility is pretty much necessary to accommodate the dependently-typed kinds of \textsc{ghc}.

\subsection{Alms}
Alms~\cite{tov_practical_2011} is an \textsc{ml}-like language based on affine types (a variant
of linear types where values can be used \emph{at most} once). It is
uses the kinds to separate affine from unrestricted arguments.

It is a case in point for kind-based systems being more complex: for
the sake polymorphism, Alms deploys an elaborate dependent kind
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

\subsection{Ownership typing à la Rust}

Rust \cite{matsakis_rust_2014} features ownership (aka uniqueness)
types. But like the original formulation of linear logic, in Rust $A$
stands for linear values, unrestricted values at type $A$ are denoted
$!A$, and duplication is explicit.

Rust quite beautifully addresses the problem of being mindful about
memory, resources, and latency. But this comes at a heavy price: Rust,
as a programming language, is specifically optimised for writing
programs that are structured using the RAII
pattern\footnote{\url{https://en.wikipedia.org/wiki/Resource_acquisition_is_initialization}}
(where resource lifetimes are tied directly or indirectly to stack
allocated objects that are freed when the control flow exits the
current lexical scope). Ordinary functional programs seldom fit this
particular resource acquisition pattern so end up being second class
citizens. For instance, tail-call optimization, crucial to the
operational behaviour of many functional programs, is not usually
sound. This is because resource liberation must be triggered when the
tail call returns.

\HaskeLL{} aims to hit a different point in the design space where
regular non-linear expressions are the norm yet gracefully scaling up
to latency-sensitive and resource starved programs is still possible.

\subsection{Related type systems}
\label{sec:related-type-systems}

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
\citeauthor{mcbride_rig_2016} makes the natural function of type $!(A⊸B) ⟹ !A⊸!B$
into an isomorphism.

In that respect, our system is closer to
\citeauthor{ghica_bounded_2014}'s. What we keep from
\citeauthor{mcbride_rig_2016}, is the typing rule of |case| (see
\fref{sec:statics}), which can be phrased in terms of linear logic as
making the natural function of type $!A⊗!B ⟹ !(A⊗B)$ into an
isomorphism. This choice is unusual from a linear logic perspective,
but it is the key to be able to use types both linearly an
unrestrictedly without intrusive multiplicity polymorphic annotation
on all the relevant types.

The literature on so-called
coeffects~\cite{petricek_coeffects_2013,brunel_coeffect_core_2014}
uses type systems similar to \citeauthor{ghica_bounded_2014}, but
with a linear arrow and multiplicities carried by the exponential
modality instead. \Citet{brunel_coeffect_core_2014}, in particular,
develops a Krivine-style realisability model for such a calculus. We are not
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
distributed and real-time environments, where latency that matters
more than throughput.

\citeauthor{wakeling_linearity_1991} propose to not attempt prompt
free of thunks and only taking advantage of linearity for managing the
lifetimes of large arrays. Our approach is similar: we advocate
exploiting linearity for operational gains on large data structures
(but not just arrays) stored off-heap. we go further and leave the
management of external (linear) data to external code, only accessing
it via an API. Yet, our language supports an implementation where each
individual constructor with multiplicity 1 can be allocated on
a linear heap, and deallocated when it is pattern matched.
Implementing this behaviour is left for future work.

\section{Conclusion and future work}

This article demonstrates how an existing lazy language, such
as Haskell, can be extended with linear types, without compromising
the language, in the sense that:
\begin{itemize}
\item existing programs are valid in the extended language
  \emph{without modification},
\item such programs retain the same semantics, and
\item the performance of existing programs is not affected.
\end{itemize}
In other words: regular Haskell comes first. Additionally, first-order
linearly typed functions and data structures are usable directly from
regular Haskell code. In such a situation their semantics is that of
the same code with linearity erased.

\calc{} was engineered as an unintrusive design, making the
integration to an existing, mature compiler with a large ecosystem
tractable. We are
developing a prototype implementation extending \textsc{ghc} with
multiplicities. The main difference between the implementation and
\calc is that the implementation is adapted to
bidirectionality: typing contexts go in, inferred multiplicities come
out (and are compared to their expected values). As we hoped, this
design integrates very well in \textsc{ghc}.

It is worth stressing that, in order to implement foreign data
structures like we advocate as a means to
provide safe access to resources or reduce \textsc{gc} pressure and
latency, we only need to modify the type system: primitives to
manipulate foreign data can be implemented in libraries using the
foreign function interface. This helps keeping the prototype lean.

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
type systems, which probably require too much change to an existing
compiler. Additionally, effect type systems would not be compatible
with Haskell's asynchronous exception
mechanism~\cite{marlow_async_exceptions_2001}.

Because we are using explicit allocators for resources such as
|withMailbox :: (MB ⊸ IO a) ⊸ IO a|, these allocators can be
responsible for safe deallocation in response to exceptions,
internally making use of the bracket operation~\cite[Section
  7.1]{marlow_async_exceptions_2001}. A full justification of this
hypothesis is left for future work.

\subsection{Fusion}
\label{sec:fusion}

Inlining is a staple of program optimisation, exposing opportunities
for many program transformation including fusion. Not every function
can be inlined without negative effects on performance: inlining a
function with two use sites of the argument may result in duplicating
a computation.

In order to discover inlining opportunities \textsc{ghc} deploys a
cardinality analysis~\cite{sergey_cardinality_2014} which determines
how many times functions use their arguments. The limitation of such
an analysis is that it is necessarily heuristic (the problem is
undecidable). Consequently, it can be hard for the programmer to rely
on such optimisations: a small, seemingly innocuous change can prevent
a critical inlining opportunity and have rippling effects throughout
the program. Hunting down such a performance regression proves
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
annotation in the cardinality analysis is left as future work.

\subsection{Extending multiplicities}

For the sake of this article, we use only $1$ and $ω$ as
possibilities.  But in fact \calc{} can readily be extended to more
multiplicities: we can follow \citet{ghica_bounded_2014} and
\citet{mcbride_rig_2016}, which work with abstract sets of
multiplicities.  In particular, in order to support dependent types,
we additionally need a $0$ multiplicity.

Applications of multiplicities beyond linear logic seem to often have
too narrow a focus to have their place in a general purpose language
such as Haskell. \Citet{ghica_bounded_2014} propose to use
multiplicities to represent real time annotations, and
\citet{petricek_coeffects_2013} show how to use multiplicities to
track either implicit parameters (\emph{i.e.} dynamically scoped
variables) or the size of the history that a dataflow program needs to
remember.

To go further still, more multiplicities may prove useful. For instance we
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
%  LocalWords:  Finalisers effectful subtyping
