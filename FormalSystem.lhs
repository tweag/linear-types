% -*- latex -*-
% Created 2016-09-15 tor 14:09
\documentclass[11pt]{article}
%include polycode.fmt
%format .         = ". "
%format forall a         = "∀" a
%format _ (a)         = "_{" a "}"
%format omega = "ω"
%format rho = "ρ"
%format pi = "π"
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

\setmonofont[Scale=0.8]{DejaVu Sans Mono}
% \setmonofont{CMU TypeWriter Text}
% \setmainfont{DejaVu Sans}
% \setmainfont{TeX Gyre Pagella}
% \setmathfont{TeX Gyre Pagella Math}
% \setmainfont{Latin Modern Roman}

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

\author{Jean-Philippe Bernardy and Arnaud Spiwack}
\date{\today}
\title{A practical lazy language with linear and unrestricted types}
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

\section{Introduction}

When one writes a program interacting with its environment, sooner or
later one needs to manage shared resources. Programming languages
typically offer three kind of facilities to help with shared resources
management which we classify as follows: ``no support'', ``dynamic
support'' or ``static support''.

The ``no support'' class leaves all the work to the programmer. It is
in particular the strategy offered by the popular Unix operating
system and its native language, C.  However, the activity of writing
resource management code such as this:
\begin{code}
do  h <- openfile "myfile" ReadMore
    -- some code that reads the file
    hClose h
\end{code}
leads easily to unsafe code with free-after-free or use-after free
errors. In concurrent settings, one may even face deadlocks.

The ``dynamic support'' class offers to dynamically detect when a
program won't use a resource, and to free it at that moment. Given such
support, the programmer will essentially omit the instruction to release the resource
(|hClose h| in the above program), and hope for the best. Automatic
dynamic management of memory is an essential constituent to the
abstractions which make modern high-level programming languages
powerful, widely known as garbage collection. Automatic dynamic
management of other resources is not as popular, but can still be
found, often under the name of ``weak references''. In Haskell,
automatic management of files is available, and is known as ``lazy IO''.
Such automatic management tends to lead to resources
being locked for too long, and thus to unnecessary resource contention.
This shortcoming is critical for scarce resources (a lock waiting to
be garbage collected will block every thread waiting on it).

The ``static support'' class has received a lot of attention in recent
years.  The idea is to forgo automatic management in flavor of safe,
but explicit management of resources, including memory. This trend is
best exemplified by the popularity of the Rust programming
language~\cite{matsakis_rust_2014}, where file-reading code such as
what follows would be written:

\begin{verbatim}
{
  let path = Path::new("hello.txt");
  let mut file = try!(File::open(&path));
  // some code that reads the file
} // the file is closed when this scope ends
\end{verbatim}

Also giving up on garabage collection offers, in particular, the following
benefits:
\begin{itemize}
\item control of \emph{how much} latency is incurred by memory management;
\item control of \emph{when} memory-management pauses occur.
\end{itemize}
Indeed garbage collection is very fast, and explicit memory management
may sometimes even be slower. Yet, fewer and more predictable pauses are
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
logic~\cite{girard_linear_1987}, we propose a linearly typed
lazy\footnote{Laziness is not an essential characteristic: a similar
  extension can be designed for a strict language. Yet the
  presentation in this article is inherently lazy: both the static and
  dynamic semantics would change slightly in a strict language} lambda
calculus (the presentation is inspired by~\cite{mcbride_rig_2016}),
which contains the simply-typed lambda calculus as a subset.

This lambda calculus can be scaled up to a full-fledged programming
language and is itself a conservative extension of Haskell. Thus we
(cheekily) call it \HaskeLL.
Concretely, in \HaskeLL,
one enjoys the convenience of programming in Haskell;
but when part of code requires more care, \emph{e.g.} because of
efficiency (Sections~\ref{sec:fusion}\&\ref{sec:orgheadline16}), or
because a foreign function needs a linear type
(Section~\ref{sec:ffi}), then one can use seamlessly the linear
features of the language, which allow more control.\improvement{Add a
  file-read example in the style of this article}

Using a type system based on linear logic (rather than uniqueness
typing or ownership typing) makes it possible to leverage the wealth
of literature of the past thirty years. Linear logic has been shown,
for instance, to be applicable to explicit memory
management~\cite{lafont_linear_1988,hofmann_in-place_,ahmed_l3_2007},
memory-efficient array computations through
fusion~\cite{bernardy_duality_2015,lippmeier_parallel_2016}, and protocol
specification (as session types)~\cite{honda_session_1993} (the
correspondence between session types and linear types is explained
in~\cite{wadler_propositions_2012}).

\section{Programming in \HaskeLL}
\label{sec:orgheadline8}

\subsection{An ILL-guided attempt}
\unsure{Should we rename weights to quantities?}

Simply using linear logic --- or, as it were, intuitionistic linear
logic, because we do not require a notion of type duality --- as a type
system would not suffice to meet our goal that a (intuitionistic,
lazy) $\lambda$-calculus be a subset of our calculus. Indeed, even if
intuitionistic $\lambda$-calculus can be embedded in linear
$\lambda$-calculus, this embedding requires an encoding. Usually, one
would have a linear arrow $A⊸B$ and the intuitionistic arrow would be
encoded as ${!}A ⊸ B$, where a value of type ${!}A$ represents an
arbitrary quantity of values of type $A$.

This encoding means that the quantity of available values must be
managed manually, and the common case (\emph{i.e.} an arbitrary quantity is
required) requires additional syntax. For instance, in the
pidgin-Haskell syntax which we will use throughout this article, we
couldn't write the following:
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

In sum, one would have to re-write all the code which uses several
instances of the same value in the $!$ co-monad: hardly a tempting
prospect.

\subsection{Putting the Bang in the arrow}

In our calculus, instead, both arrow types are primitive. To be
precise, in a style proposed by McBride~\cite{mcbride_rig_2016}, the
arrow type is parametrized by the amount of its argument it requires:
\begin{itemize}
\item $A →_1 B$ is the linear arrow $A ⊸ B$
\item $A →_ω B$ is the intuitionistic\todo{It is weird to call it like
    that, because intuitionism is a constructive reaction to classicism; and ILL is certainly intuitionistic in that sense.} arrow
  $A → B$
\end{itemize}

The first main benefit of this approach is that all the code already
written, assuming an $ω$-sized supply of everything, can work out of
the box.

The second benefit is that one can write linear code whenever it is
possible, and use it in unrestricted contexts anyway. The following
example illustrates.

\begin{code}
data List a where
  [] :: List a
  (:) :: a ⊸ List a ⊸ List a
\end{code}
The above data declaration defines a linear version of the list
type. That is, given \emph{one} instance of a list, one will obtain
exactly \emph{one} instance of each of the items contained inside it.
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

Operationally, this means that the resulting list does not need to
live on a GC'ed heap\footnote{even though it can} --- instead it can
be put on an explicitly managed heap (which we call the linear heap in
what follows). If so, that list can thus be deallocated exactly at the
point of its consumption. In a lazy language, the thunks on the linear
heap can thus even free themselves.

Yet, conceptually, if one has a quantity $ω$ for both inputs, one can
call $ω$ times |(++)| to obtain $ω$ times the concatenation.
Operationally, having an $ω$ quantity of the inputs implies that they
reside on the GC heap, and thus can be shared as much as
necessary. Constructing $ω$ times the output means to put it on the GC
heap as well, with all the usual implications in terms of laziness and
sharing.

A function may legitimately demand $ω$ times its input. For example
the function repeating indefinitely its input will have the type:

\begin{code}
cycle :: List a → List a
\end{code}

Operationally, |cycle| requires its argument to be on the GC heap.  In
practice, libraries will never provide $ω$ times a scarce resource
(eg. a handle to a physical entity); such a resource will thus never
end up in the argument to |cycle|.

While automatic scaling from $1$ to $ω$ works well for first-order
code, higher-order programs need polymorphism over weights. For
example, the standard |map| function
\begin{code}
map f []      = []
map f (x:xs)  = f x : map f xs
\end{code}
can be given the two incomparable following types: |(a ⊸ b) -> List a
⊸ List b| and |(a -> b) -> List a -> List b|. The type subsuming both versions is
|∀rho. (a -> _ rho b) -> List a -> _ rho List b|. \improvement{Can we show that a principal type always exists? This would probably require a lattice structure on weights?}

Likewise, function composition can be given the following type:
\begin{code}
(∘) :: forall pi rho. (b → _ pi c) ⊸ (a → _ rho b) → _ pi a → _ (pi rho) c
(f ∘ g) x = f (g x)
\end{code}
What the above type says is that two functions of arbitrary linearities $ρ$
and $π$ can be combined into a function of linearity $ρπ$.

\section{Sharing linear data}

The |Bang| type, used above, can be defined in \HaskeLL{} like so:

\begin{code}
data Bang a where
  Bang :: a → Bang a
\end{code}

The above type is useful for example to return a sharable reference even
when a function is called just once. In particular, copiable
can be captured with the following class:
\begin{code}
data Copiable a where
  copy :: a → Bang a
\end{code}
It turns out that all data structures are copiable. For example:
\begin{code}
instance Copiable a => Copiable (List a) where
  copy [] = Bang []
  copy (x:xs) = case (copy x, copy xs) of
    (Bang x', Bang xs') -> Bang (x':xs')
\end{code}

Equipped with the above, one can create shareable references while
without escaping to the unrestricted world. Doing so is necessary when
one does not only want the static guarantees of linearity, but also
its dynamic benefits. \todo{add forward references or move this
  section to a more appropriate place.}

\section{\calc{} statics}
\subsection{Typing contexts}
\label{sec:typing-contexts}

Each variable in typing contexts is annotated with the number of times
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

The types of our calculus (see \fref{fig:syntax}) are simple
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
  $\data \varid{Bang} A \where \varid{Bang} A→_ω \varid{Bang} A$ is
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
use it in Section~\ref{sec:orgheadline16} to define a compositional
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

The typing judgement \(Γ ⊢ t : A\) ought to be read as follows: the term $t$ consumes $Γ$ and
builds \emph{exactly one} $A$. Contrary to~\textcite{mcbride_rig_2016}, we provide
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
as a subset of \calc{}. Indeed, recall the example from the
beginning of Section~\ref{sec:orgheadline8} which had us write |dup
(Bang (id (Bang 42)))|. Thanks to the application rule we have
instead:\improvement{maybe work a little on the presentation of this
  example}
$$
\inferrule
{\inferrule
  {\inferrule
    {\inferrule{ }{x :_ω A ⊢ x : A}\text{var} \qquad \inferrule{ }{x :_ω A ⊢ x : A}\text{var}}
    {x :_ω A ⊢ Tensor x x : Tensor A A}\text{con}}
  {⊢ λ x. Tensor x x : A →_ω Tensor A A}\text{abs} \qquad \inferrule{\vdots}{⊢ id 42}}
{()+ω() ⊢ (λ x. Tensor x x) (id 42)}\text{app}
$$
In the application rule the promotion rule of linear logic is applied
implicitly.
$$\inferrule{{!}Γ ⊢ A}{{!}Γ ⊢ {!}A}$$
where ${!}Γ$ is a context with all the hypotheses of the form ${!}A$
for some $A$.

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
$ω$-weighted variables: that is, it allows variables of weight
$ω$---and only of weight $ω$---not to be used. Pushing weakening to
the variable rule is classic in many lambda calculi, and in the case
of linear logic, dates back at least to Andreoli's work on
focusing~\cite{andreoli_logic_1992}. Note that the judgement
$x :_ω A ⊢ x : A$ is an instance of the variable rule, since
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
well-typed
\begin{code}
  data (⊗) a b where
    (,) : a ⊸ b ⊸ a⊗b

  first  :: a⊗b → a
  first (a,b)  = a

  snd  :: a⊗b → b
  snd (a,b)  = b
\end{code}
These projections are a small deviation from linear logic: the
existence of these projections mean that ${!}(A⊗B)$ is isomorphic to
${!}({!}A⊗{!}B)$. While this additional law may restrict the
applicable models of our calculus (hence may be inconvenient for some
applications), it is key to retro-fitting linearity in an existing
language: if we interpret the weights on the arguments of existing
constructor to be $1$ while the weights on the arguments of existing
functions to be $ω$, the typable programs are exactly the same as an
intuitionistic $λ$-calculus.
\info{Remark: the reason why
  we can have ${!}(A\otimes B) \simeq {!}({!}A\otimes{!}B)$ is that we
  have a model in mind where all sub-data is boxed (and managed by GC)
  if the data is managed by GC. In a model where sub-data is unboxed,
  we would need the ability to copy sub-data (\emph{chunks of data})
  into the GC-ed heap, which is not necessarily available for all
  data. So this extension of linear logic fits our Haskellian model
  rather snugly. It is not the only possible path, however.}  \improvement{show free, dup and copy on booleans
  and peano-numbers}

\subsection{Examples of simple programs and their types}
\unsure{Scrap this section?}
In order to assess the power of our language, let us consider a few
simple programs and the types that they inhabit.

\paragraph{K combinator}

The $\lambda$-calculus expression $k ≝ λx. λy. x$ can be elaborated in our system to have either the type
$A ⊸ B → A$ or $A → B → A$. However, the first type subsumes the
second one, because when we heave $ω$ times $A$, we can always call
$k$ anyway and ignore the rest of $A$'s. (In this situation, we can
also call $ω$ times $k$). The lesson learned is that when a variable is used
(syntactically) just once, it is always better to give it the
weight 1.\inconsistent{It is always better to use $⊸$ if there is a
  subtyping relation. Since we have weight polymorphism instead, $k$
  should probably be given a polymorphic type to avoid the need to
  $\eta$-expand $k$ sometimes.}

\paragraph{Second order Identity}

Similarly $a ≝ λf.λx.f x$ could inhabit all the following types:
$(A → B) → A → B$,
$(A → B) ⊸ A → B$ and
$(A ⊸ B) ⊸ A ⊸ B$.

As per the lesson learned in the previous paragraph, the first type is
dominated by the second one. However the remaining two types are
incomparable. If we want to find a most general type we need to
abstract over the weight of $A$:

\[ λf. λx. f x : (A →_ρ B) → A →_ρ B.\]
\todo{This is isn't true, strictly speaking}

\paragraph{Function composition}
The need for weight abstraction typically occurs in all higher order
functions.  In particular, function composition inhabits a wealth of
incomparable weight-monomorphic types. Yet they can subsumed by
abstracting over the linearities of the input functions, as follows:

\[ λf. λg. λx. f (g x) : (B →_π C) ⊸ (A →_ρ B) →_π A →_{πρ} C\]
\todo{This is isn't true, strictly speaking}

\improvement{
example of ill-typed programs due to linearity violation,
with tentative error messages.
}

\section{Applications}
\label{sec:ghc}

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
Many languages with session types offer
duality at their core, and conveniently make negation involutive. We
neither rely on nor provide this feature: it is not essential to
precisely and concisely describe protocols.  Additionally, we have
no primitive $⊥$ type in \HaskeLL{}: instead we assume that it is an
abstract type provided by a library, together with a combinator
which executes the embedded computation:
\begin{code}
type ⊥ -- abstract
runComputation :: ⊥ ⊸ IO ()
\end{code}
Assuming the above signature, we can define a protocol for a simple
`bank-account' server. We do so by simultaneously defining two dual types,
corresponding to either the point of view of the server or the client.
\begin{code}
data Status = Success | Failure
data Client where
  Deposit  :: Nat -> Dual Server ⊸ Client
  Withdraw :: Nat -> Dual (Status ⊗ Server) ⊸ Client
type Server = Dual Client
\end{code}
The |Client| type describes the possible behaviours of the
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
\item The implementation will not `hold onto' stale server/client
  states any longer than strictly necessary: no memory leak can occur.
\end{enumerate}
\subsection{FFI}
\label{sec:ffi}

It is not uncommon for Haskell libraries to be shims over libraries
written in C. Sometimes, the underlying C library is also non
re-entrant. That is, they have a single global context, thus if ones
tries to call the C library several times from different logical
contexts, one will get incorrect results. A typical attempt to this
issue involves
1. using a monadic interface to the library and
2. having an existentially bound a type parameter in the type:

\begin{code}
type M s a
instance Monad s

primitive :: M s X
runLowLevel :: M s a -> IO x
\end{code}

This solution is adequate as long as one refrains from calling
\begin{code}
forkIO :: IO a -> IO ()
\end{code}
Indeed, if one uses |forkIO|, there is a risk to call |runLowLevel|
several times in parallel.

Using linear types, one may instead provide an explicit and unique
instance of the context.
\begin{code}
type Context
initialContext :: _ 1 Context
\end{code}

The |Context| type will not have any runtime representation on the
Haskell side.  It will only be used to ensure that primitive
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
One of the usage of linear types is to make memory management
(semi-)explicit. As an illustration we provide two possible APIs to
manipulate randomly addressable memory regions (so called ``byte
arrays'' in GHC parlance). We also propose a possible implementation
strategy for the primitives, and argue briefly for correctness.

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

The key primitive in the above API is |withNewByteArray|, whose first
argument is the size of an array to allocate. It takes a continuation
where \emph{one} reference to the byte array is
available. Operationally, the function starts by allocating a byte
array of the requested size \emph{on a non GC heap} and call the
continuation. The types of the various primitives are chosen to ensure
memory safety. Crucially, the continuation needs to produce a |Bang|
type. This signature ensures that the continuation cannot return a
reference to the byte array.  Indeed, it is impossible to transform a
$1$-weighted object into an $ω$-weighted one, without copying it
explicitly. Not returning the byte array is critical, because the
|withNewByteArray| function may be called $ω$ times; in which case its
result will be shared.

Many functions take a |MutableByteArray| as argument and produce a new
|MutableByteArray|. Such functions can perform in-place updates of the
array (even though we remark that the |MutableByteArray| is not a
reference type) because linearity ensures that it cannot be shared.

Finally, |freezeByteArray| turns a linear |MutableByteArray| into a
shareable |ByteArray|. It does so by moving the data from the linear
heap onto the GC heap. It consumes the static |MutableByteArray|,
so that no further function can access it. In particular, such a frozen
byte array can be returned by the argument to |withNewByteArray|:
\begin{code}
  withNewByteArray n freezeByteArray :: ByteArray
\end{code}

\todo{Add splitByteArray?}

\subsubsection{Version 2}

A possible shortcoming of the above API is that it forces to write
allocating code in CPS. An alternative API is the following.

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

\todo{Why do freeze/free need the heap access?}
\subsection{Fusion}
\label{sec:fusion}

A popular optimization for functional languages, and in particular
GHC, is \emph{shortcut fusion} \cite{gill_short_1993}.  Shortcut
fusion relies on the custom rewrite rules, and a general purpose
compile-time evaluation mechanism.

Concretely:
\begin{enumerate}
\item Rewrite rules transform structures which use general recursion
  into a representation with no recursion (typically church encodings)
\item The inliner kicks in and fuses compositions of non-recursive
  functions
\item Unfused structures are reverted to the original representation.
\end{enumerate}

The problem with this scheme is that it involves two phases of
heuristics (custom rewrite rules and evaluator), and in practice
programmers have difficulties to predict the performance of any given
program subject to shortcut fusion. It is not uncommon for a compiler
to even introduce sharing where the programmer doesn't expect it,
effectively creating a memory leak
(\url{https://ghc.haskell.org/trac/ghc/ticket/12620}).

A partial remedy to this situation is to stop relying on rewrite rules,
and use directly non-recursive representations. Doing so is nowadays
popular in libraries for efficient programming in Haskell. \todo{cite
  eg. feldspar, accelerate, ...}

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
consume memory and are never implemented using recursion. Thus, one
eventually gets code which is known to be fused. For instance, in the
following example from Lippmeier et al., neither the source nor the
sink represent data in memory.

\begin{code}
copySetP :: [FilePath] -> [FilePath] -> IO ()
copySetP srcs dsts = do
  ss <- sourceFs srcs
  sk <- sinkFs   dsts
  drainP ss sk
\end{code}

However, one then faces two classes of new problems.

First, any non-linear (precisely non-affine) use of such a
representation will \emph{duplicate work}. For example, one can write
the following piece of code, but the |expensiveComputation| will be
run twice, perhaps unbeknownst to the programmer.

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
|srcs| have weight 1, so has |ss|, and thus it cannot be shared in the
following lines. The programmer has then the choice of either: copying
the contents of |srcs| or duplicating the computation, and this choice
must be written explicitly.
Programming streaming libraries with explicit linearity has been
explored in detail by \textcite{bernardy_duality_2015}.

\section{\calc{} dynamics}
\label{sec:orgheadline16}

Supporting the examples of~\fref{sec:ghc} would require only changes to
an Haskell implementation: only the type system for \fref{sec:ffi} and
\fref{sec:primops}, while \fref{sec:fusion} only requires additional
annotations in the optimization phase.

If one is willing to dive deeper and modify the runtime system, a
further benefit can be reaped: prompt deallocation of thunks. While
this extension of the runtime system is not necessary to benefit from
linear types, the dynamic semantics presented in this section can also
help give confidence in the correctness of the extensions
of~\fref{sec:ghc}.

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
      &||  r_q x\\
      &||  λπ. r\\
      &||  r p\\
      &||  c x₁ … x_n\\
      &||  \case r {c_k  x₁ … x_{n_k} → r_k}\\
      &||  \flet x_1 =_{q₁} r₁ … x_n =_{q_n} r_n \fin r
  \end{align*}

  \figuresection{Translation of typed terms}

  \begin{align*}
    (λ(x:_qA). t)^* &= λ(x:_qA). (t)^* \\
    x^*             &= x \\
    (t_q  x )^*     &= (t)^*_q  x \\
    (t_q  u )^*     &= \flet y =_{q} (u)^* \fin (t)^*_q  y \\
    c_k  t₁ … t_n   &= \flet x₁ =_{q_1} (t₁)^*,…, x_n =_{q_n} (t_n)^*
                      \fin c_k x₁ … x_n
  \end{align*}
  \begin{align*}
    (\case t {c_k  x₁ … x_{n_k} → u_k})^* &= \case {(t)^*} {c_k  x₁ … x_{n_k} → (u_k)^*} \\
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

Compared to \citeauthor{launchbury_natural_1993}'s original, our
semantics exhibits the following salient points:
\begin{itemize}
\item The heap is annotated with weights. Variables with weight $ω$
  point to the the GC heap, while variables with weight $1$ point to
  the linear heap.
\item We add a weight in the reduction relation, corresponding to the
  (dynamic) quantity of values to produce.
\item The rules for \emph{variable} and \emph{let} are changed to
  account for weights.
\end{itemize}

The weight in the reduction relation is used to interpret $\flet =_1 …$
bindings into allocations on the proper heap.  Indeed, in $ω$ contexts,
$\flet =_1 …$ must allocate on the GC heap, not on the linear
one. Indeed, consider the example:

\begin{code}
let f = _ omega (\y : _ 1 () -> case y of () -> let z = _ 1 True in z) in
let a = _ rho f ()
\end{code}

The function \varid{f} creates some data. When run in a linear context, \varid{f}
allocates \varid{z} on the linear heap. When run in an unrestricted context, it
must allocate \varid{z} on the GC heap. So, its behavior depends the value of $ρ$.

\begin{figure}
  \begin{mathpar}
    \inferrule{ }{Γ : λπ. t ⇓_ρ Γ : λπ. t}\text{w.abs}


    \inferrule{Γ : e ⇓_ρ Δ : λπ.e' \\ Δ : e'[q/π] ⇓_{ρ} Θ : z} {Γ :
      e q ⇓_ρ Θ : z} \text{w.app}

    \inferrule{ }{Γ : λx. e ⇓_ρ Γ : λx. e}\text{abs}


    \inferrule{Γ : e ⇓_ρ Δ : λy.e' \\ Δ : e'[x/y] ⇓_{qρ} Θ : z} {Γ :
      e_q x ⇓_ρ Θ : z} \text{application}

    \inferrule{Γ : e ⇓_ω Δ : z}{(Γ,x ↦_ω e) : x ⇓_ρ (Δ;x ↦_ω z) :
      z}\text{shared variable}


    \inferrule{Γ : e ⇓_1 Δ : z} {(Γ,x ↦_1 e) : x ⇓_1 Δ :
      z}\text{linear variable}


    \inferrule{(Γ,x_1 ↦_{q_1ρ} e_1,…,x_n ↦_{q_nρ} e_n) : e ⇓_ρ Δ : z}
    {Γ : \flet x₁ =_{q₁} e₁ … x_n =_{q_n} e_n \fin e ⇓_ρ Δ :
      z}\text{let}

    \inferrule{ }{Γ : c  x₁ … x_n ⇓_ρ Γ : c  x₁ …
      x_n}\text{constructor}


    \inferrule{Γ: e ⇓_ρ Δ : c_k  x₁ … x_n \\ Δ : e_k[xᵢ/yᵢ] ⇓_ρ Θ : z}
    {Γ : \case e {c_k  y₁ … y_n ↦ e_k } ⇓_ρ Θ : z}\text{case}
  \end{mathpar}

  \caption{Dynamic semantics}
  \label{fig:dynamics}
\end{figure}
Remark: the \emph{unrestricted variable} rule also triggers when the
weight is 1, thus effectively allowing linear variables to look on the
GC heap. This behavior allows an occurrence of a linear variable to
work in an unrestricted contexts, in turn justifying the $1 + ω = ω$
rule.
\todo{Works only on weight-closed terms}
\paragraph{Theorem: The GC heap contains no references to the linear heap}
(This result is critical for heap consistency.)

Lemmas:
\begin{itemize}
\item If the weight is $ω$, then the linear heap is empty.
%  A
% consequence of this is that we should have main ::1 IO () --
% otherwise it's impossible to have anything in the linear heap.

% Furthermore, in order to use IO in any reasonable way, we need a
% 'linear do notation'.
\item Every variable which is bound in the linear heap is statically
  bound with weight $1$.
\item Conversely: every variable bound statically with weight $ω$ is
  bound in the GC heap.
\end{itemize}


% Proof:
% 1. The only place where the heap is populated is in let. So we check let. We put things in the GC heap when πρ = ω.
%    a. π = ω. Statically, the expression can only depend on the ω context, so we can't create any reference to the linear heap.
%    b. ρ = ω. In this case, by lemma 1. the linear heap is empty, and thus it's impossible to link to anything in it.

% relation: Δ||Γ;Φ ⊢ e :_ρ A   ≜  Δ ⊢ letω Γ in let1 Φ in e :_ρ A

% theorem: if Γ;Φ : e ⇓_ρ Δ,Ψ : z then ∀Ξ,Θ,Α.   Θ||Γ;(Φ-Ξ) ⊢ e :_ρ A  ⇒  Θ||Δ;(Ψ-Ξ) ⊢ z :_ρ A


% unrestricted variable case:

% Need to prove:

%   Θ,x:T||Γ;(Φ-Ξ) ⊢ e :_ρ T  ⇒  Θ,x:T||Δ;(ψ-Ξ) ⊢ z :_ρ T
% ──────────────────────────────────────────────────────
%  Θ||Γ,x↦e;(Φ-Ξ) ⊢ x :_ρ T  ⇒  Θ||Δ,x↦z;(ψ-Ξ) ⊢ z :_ρ T

% case case:

% Need to prove:

% Ψ = free vars ek - y + x + Z
% ? = free vars ek - y

% Σ||Γ;Φ-(Z+?) ⊢ e :_ρ D ⇒ Σ||Δ;Ψ-(Z+?) ⊢ ck x :_ρ D
% Σ||Δ;Ψ-Z ⊢ ek[x/y] :_ρ A ⇒ Σ||θ;Ξ-Z ⊢ z :_ρ A
% ─────────────────────────────────────────────────────────────
% Σ||Γ;Φ-Z ⊢ case e of {ck y -> ek} :_ρ A  ⇒ Σ||Θ,Ξ-Z ⊢ z :_ρ A


Yet, the following example may, at first glance, look like a counter
example where |x| is in the non-GC heap while |y| is in the
GC-heap and points to |x|:
\begin{code}
data () where () :: ()

let x = _ 1 ()
let y = _ omega ( case x of { () -> () })
in ()
\end{code}
However, while |()| can indeed be typed as $⊢ () :_ω ()$, the
typing rule for 'case' gives the same weight to the case-expression as
a whole as to the scrutinee (|x| in this case). Therefore
|case x of { () -> ()}| has weight $1$. \improvement{It's very unclear what this paragraph is trying to convey.}

\section{Comparison with other techniques}

\subsection{Linearity as a property of types vs. linearity as a property of bindings (variables)}

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
paper.). In sum, session types classify 'live' sessions with
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

\subsection{Weights in type derivation}

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
(λ (dup : _ ω a ⊸ (a ⊗ a) ) . dup) (λx. (x,x))
\]

Effectively, in \citeauthor{mcbride_rig_2016}'s system, one cannot use
abstractions while retaining the linearity property.

\subsection{TODO}

\todo{\textcite{wakeling_linearity_1991}}

\section{Extensions and Future Work}

unsure{Weight inference? Polymorphism? Magic |copy| of data structures?}

\subsection{More Weights}

To keep things concrete, we have limited the constants of the language
of weights to $1$ and $ω$. Yet, we could have more constants.  For
example, we could add $α$ to represent affine variables (usable zero
or once). In this situation we would have $α + 1 = ω$, $α · ω = ω$,
and the variable rule should be extended to $α$-contexts. Similarly one
can add a $0$, as \textcite{mcbride_rig_2016} does, and in turn
support dependent types.

We can even make the set weight constants = $2^ℕ$, with the obvious
operations, and the variable rule adapted accordingly.

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
%  LocalWords:  dsts sourceFs sinkFs drainP expensiveComputation
%  LocalWords:  duplications bernardy deallocate morris latencies
%  LocalWords:  doSomethingWithLinearHeap untyped
