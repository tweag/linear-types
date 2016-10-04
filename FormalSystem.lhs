% -*- latex -*-
% Created 2016-09-15 tor 14:09
\documentclass[11pt]{article}
%include polycode.fmt
%format .         = ". "
%format forall a         = "∀" a
%format _ a         = "_{" a "}"
%format omega = "ω"
%format rho = "ρ"
%format pi = "π"
%subst keyword a = "\mathsf{" a "}"
\usepackage[backend=biber,citestyle=authoryear,style=alphabetic]{biblatex}
\bibliography{PaperTools/bibtex/jp.bib}
\usepackage{fixltx2e}
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
\usepackage{mathpartir}
\usepackage{fontspec}
\usepackage{unicode-math}
\setmonofont[Scale=0.8]{DejaVu Sans Mono}
% \setmonofont{CMU TypeWriter Text}
% \setmainfont{DejaVu Sans}
% \setmathfont{TeX Gyre Pagella Math}
\newcommand{\case}[3][]{\mathsf{case}_{#1} #2 \mathsf{of} \{#3\}^m_{k=1}}
\newcommand{\data}{\mathsf{data} }
\newcommand{\inl}{\mathsf{inl} }
\newcommand{\inr}{\mathsf{inr} }
\newcommand{\flet}[1][]{\mathsf{let}_{#1} }
\newcommand{\fin}{ \mathsf{in} }
\newcommand{\varid}{\mathnormal}
\newcommand{\susp}[1]{⟦#1⟧}
\usepackage[dvipsnames]{xcolor}
\usepackage[colorinlistoftodos,prependcaption,textsize=tiny]{todonotes}
\usepackage{xargs}
\newcommandx{\unsure}[2][1=]{\todo[linecolor=red,backgroundcolor=red!25,bordercolor=red,#1]{#2}}
\newcommandx{\info}[2][1=]{\todo[linecolor=OliveGreen,backgroundcolor=OliveGreen!25,bordercolor=OliveGreen,#1]{#2}}
\newcommandx{\change}[2][1=]{\todo[linecolor=blue,backgroundcolor=blue!25,bordercolor=blue,#1]{#2}}
\newcommandx{\inconsistent}[2][1=]{\todo[linecolor=blue,backgroundcolor=blue!25,bordercolor=red,#1]{#2}}
\newcommandx{\improvement}[2][1=]{\todo[linecolor=Plum,backgroundcolor=Plum!25,bordercolor=Plum,#1]{#2}}
\newcommandx{\resolved}[2][1=]{\todo[linecolor=OliveGreen,backgroundcolor=OliveGreen!25,bordercolor=OliveGreen,#1]{#2}} % use this to mark a resolved question
\newcommandx{\thiswillnotshow}[2][1=]{\todo[disable,#1]{#2}} % will replace \resolved in the final document

\newtheorem{definition}{Definition}
\newtheorem{lemma}{Lemma}

\author{Jean-Philippe Bernardy and Arnaud Spiwack}
\date{\today}
\title{Linear and unrestricted at the same time}
% A practical lazy language with linear and unrestricted types.
\hypersetup{pdflang={English}}

% XXX: Placeholders: remove when bibliography is finished
\newcommand{\citationneeded}{[?]}
\newcommand{\TODO}[1]{{\footnotesize\it <TODO: #1>}}

% XXX: fixes a bibliographic link
\newcommand{\HREF}[2]{\href{#1}{#2}}

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

\improvement{I think that it'd be better to have the general case
  (resource management) come first.}

Garbage collection is an
essential constituent to the abstractions which make modern high-level
programming languages powerful. However, in recent years, high-level
languages which forgo garbage collection have gotten a lot of
attention. This trend is best exemplified by the popularity of the
Rust programming language~\citationneeded.

The reason for such a desire for the absence of garbage collection is
control:
\begin{itemize}
\item control of \emph{how much} latency is incurred by memory management;
\item control of \emph{when} memory-management pauses occur.
\end{itemize}
Indeed garbage collection is very fast, and explicit memory management
may sometimes even be slower. But fewer and more predictable pauses are
important when operating under real-time constraints or in a
distributed systems when a pause on one process can make all the other
processes wait for the slower process to reach completion.

A further benefit of safe explicit memory management is that it can be
extended to safe \emph{resource} management. Indeed, in garbage
collected language, management of resources such as files descriptors,
database handles, and locks is usually explicit (resources have to be
manually closed). The reason is that such resource are scarce (of
locks, in particular, there is one of each kind), and leaving the job
to free them to the garbage collector tends to lead to resources being
open for too long and unnecessary resource contention (a lock waiting
to be garbage collected will block every thread waiting on it). In
garbage-collected languages, resource management is usually left in
the care of the programmer, and can be used unsafely. \TODO{discussion
  of combinators which address this and their limitations}

Languages with safe explicit memory management tend to have vastly
different type systems (such as the ownership and borrowing typing of
Rust). This observation may induce the belief that abandoning the
comfort and convenience of \textsc{ml}-family languages is required to benefit
from the increased control allowed by garbage-free languages.

This article posits that, to the contrary, existing programming
languages, such as Haskell~\cite{marlow_haskell_2010}, can be extended
to incorporate safe explicit memory and resource management, and gain
a measure of control on garbage-collection pauses. Taking cues from
linear logic~\cite{girard_linear_1987}, we propose a linearly typed
lazy\footnote{It is not essential that the language is lazy, a similar
  extension can be designed for a strict language. But the
  presentation in this article is inherently lazy: both the static and
  dynamic semantics would change slightly in a strict language}
programming language (the presentation is inspired by~\TODO{McBride:
  rig https://personal.cis.strath.ac.uk/conor.mcbride/pub/Rig.pdf}),
whose main characteristic is to contain a regular programming
language -- a simplified version of Haskell -- as a subset.

Concretely, in such a programming language, one enjoys the convenience
of programming in Haskell most of the time. But when part of code
requires more care, \emph{e.g.} because of efficiency
(Sections~\ref{sec:fusion}\&\ref{sec:orgheadline16}), or because a
foreign function needs a linear type (Section~\ref{sec:ffi}), then one
can use seamlessly the linear feature of the language, which allow
more control.

\TODO{Applications:
\begin{itemize}
\item Explicit memory
  management~\cite{lafont_linear_1988}\cite{hofmann_in-place_}\TODO{http://www.cs.cornell.edu/people/fluet/research/lin-loc/TLCA05/tlca05.pdf}
\item Fusion/composable array computations without intermediate
  allocations~\cite{bernardy_duality_2015},\TODO{Polarized Data
    Parallel Data Flow, FHPC 2016, Lippmeier\&al}
\item Protocol specification (session types)~\TODO{honda: http://www.kurims.kyoto-u.ac.jp/~kyodo/kokyuroku/contents/pdf/0851-05.pdf}. The correspondence between
  session types and linear types is explained in~\cite{wadler_propositions_2012}
\end{itemize}}

% - the problem
%   - applications of linear types (usual)
%   - integration with existing language (limit explosion of types --- and thus of code)

% - examples
%   - protocol?
%   - primops
%   - linear stuff used in unrestricted context

\section{Statics}
\label{sec:orgheadline8}
\subsection{Weights}
\unsure{Should we rename weights to quantities?}

In our calculus, each variable in the context is annotated with the
number of times that the program must use the variable in question.
We call this number of times the \emph{weight} of the variable.

\begin{align*}
  p,q &::= 1 ~||~ ω ~||~ π ~||~ p+q ~||~ p·q
\end{align*}

A weight can either be a constant ($1$ or $ω$), a variable (ranged
over by the metasyntactic variables \(π\) and \(ρ\)), a product or a
sum.  When the weight is $1$, the program must consume the variable
exactly once. When the weight is $ω$, it may consume it any number of
times (possibly zero).

Weights are equipped with an equivalence relation $(=)$ which contains
the following laws:

\begin{itemize}
\item $+$ and $·$ are associative and commutative
\item $1$ is the unit of $·$
\item $·$ distributes over $+$
\item $ω · ω = ω$
\item $1 + ω = ω$
\item $1 + 1 = ω$
\item $ω + ω = ω$
\end{itemize}

Thus, weights have a ring-like algebra.

\subsection{Contexts}

As we wrote above, every variable binding in a context is equipped
with a weight, additionally to the type:

\begin{align*}
  Γ,Δ & ::=\\
    & ||  x :_q A, Γ & \text{weight-annotated binder} \\
    & ||     & \text {empty context}
\end{align*}

Because weights have a ring-like structure, contexts have a module
structure. In particular, we can define context addition and context
scaling.

\begin{definition}[Context addition]~
\begin{itemize}
\item When a variable appears on both input contexts, we add the weights in
the result:

\((x :_p A,Γ) + (x :_q A,Δ) = x :_{p+q} A, (Γ+Δ)\)

\item otherwise we propagate:

\((x :_p A,Γ) + Δ = x :_p A, Γ+Δ\)   \hfill   \(x ∉ Δ\)
\end{itemize}
\end{definition}

\begin{definition}[Context scaling]
\begin{displaymath}
p(x :_q A, Γ) =  x :_{pq} A, pΓ
\end{displaymath}
\end{definition}

\begin{lemma}[Contexts form a module]
  \begin{align*}
 p (Γ+Δ) &=p Γ+p Δ\\
 (p+q) Γ&=p Γ+q Γ \\
 (pq) Γ&=p (q Γ)\\
 1 Γ&=Γ
  \end{align*}
\end{lemma}

Additionally, context addition is commutative.
\subsection{Types}

\begin{definition}[Syntax of types]
\begin{align*}
  A,B &::=\\
      & ||  A →_q B &\text{function type}\\
      & ||  ∀ρ. A &\text{weight-dependent type}\\
      & ||  D &\text{data type}
\end{align*}
\end{definition}

The weighted function type is a generalization of the intuitionistic
arrow and the linear arrow. In fact in the context of this paper, we
will define them as such:
\begin{itemize}
\item \(A → B ≝  A →_ω B\)
\item \(A ⊸ B ≝ A →_1 B\)
\end{itemize}
In general, the intuition behind the weighted arrow \(A →_q B\) is
that you can get a \(B\) if you can provide a quantity \(q\) of \(A\).
Note in particular when one has $x :_ω A$ and $f :_1 A ⊸ B$,
the call $f x$ is well-typed.

The calculus also features abstraction over weights, and thus we can
construct weight-dependent types using the syntax $∀ρ. A$.

\begin{definition}[Syntax of data type declaration]
\begin{align*}
\mathsf{data} D  \mathsf{where} \left(c_k :: A₁ →_{q₁} ⋯    A_{n_k} →_{q_{n_k}} D\right)^m_{k=1}
\end{align*}

(\(D\) has \(m\) constructors \(c_k\), for \(k ∈ 1…m\)).

We will give special typing rules for constructors, but one could
equivalently add a constant per constructor $c_k$, with the type
$A₁ →_{q₁} ⋯ A_{n_k} →_{q_{n_k}} D$.
\end{definition}
Such declarations cannot occur in expressions; thus the weights $q_i$
will either be $1$ or $ω$.

Note the following special cases:
\begin{itemize}
\item The type $\data \varid{Pair} A B = \varid{Pair} ωA ωB$ is isomorphic to the intuitionistic product (Usually written $A×B$)
\item The type $\data \varid{Tensor}  A  B = \varid{Pair}  1A  1B$ is isomorphic to the linear tensor product (Usually written $A⊗B$)
\item The type $\data \varid{Bang} A = \varid{Box}  ωA$ is isomorphic to the exponential (Usually written $!A$)
\end{itemize}

\begin{definition}[Syntax of terms]
\begin{align*}
e,s,t,u & ::= \\
    & ||  x & \text{variable} \\
    & ||  λ(x:_qA). t & \text{abstraction} \\
    & ||  t_q s & \text{application} \\
    & ||  λπ. t & \text{weight abstraction} \\
    & ||  t p & \text{weight application} \\
    & ||  c t₁ … t_n & \text{data construction} \\
    & ||  \case[p] t {c_k  x₁ … x_{n_k} → u_k}  & \text{case} \\
    & ||  \flet x :_{q₁}A₁ = t₁ … x:_{q_n}A_n =_{q_n} t_n \fin u & \text{let}
\end{align*}
\end{definition}


Remark: we often omit the weight $q$ in an application, because it is
usually obvious from the context.

We have a typing judgement \(Γ ⊢ t : A\), inductively defined by the
following rules.  The intuition behind this judgement is: can
construct \emph{exactly one} value of type $A$ from $Γ$, using $t$'s
recipe. We do not define a judgement to denote that we can construct a
given quantity $q$ of type $A$, because we can instead use the
judgement $Δ ⊢ t : A$ together with the constraint $Γ = pΔ$ to
indicate this situation. The intuition behind this choice is that one
can simply call $q$ times $t$, each time consuming the $q$-th part of
$Γ$.

\begin{definition}[Typing judgement]
\begin{mathpar}
\inferrule{ }{ωΓ + x :_1 A ⊢ x : A}\text{var}

\inferrule{Γ, x :_{q} A  ⊢   t : B}
          {Γ ⊢ λ(x:_qA). t  :  A  →_q  B}\text{abs}

\inferrule{Γ ⊢ t :  A →_q B  \\   Δ ⊢ u : A}
          {Γ+qΔ ⊢ t_q u  :  B}\text{app}

\inferrule{Δᵢ ⊢ tᵢ : Aᵢ \\ \text {$c_k$ is a constructor of $D$ with arguments $Aᵢ$ and weights $qᵢ$}}
          {\sum_i qᵢΔᵢ ⊢ c_k  t₁ … t_n :  D}\text{con}

\inferrule{Γ   ⊢  t  : D  \\ Δ, x₁:_{pqᵢ} Aᵢ, …, x_{n_k}:_{pq_{n_k}} A_{n_k} ⊢ u_k : C \\ \text{with each $c_k$ as above}}
          {pΓ+Δ ⊢ \case[p] t {c_k  x₁ … x_{n_k} → u_k} : C}\text{case}


\inferrule{Γᵢ   ⊢  tᵢ  : Aᵢ  \\ Δ, x₁:_{q₁} A₁ …  x_n:_{q_{n}} A_n ⊢ u : C }
          { Δ+\sum_i qᵢΓᵢ ⊢ \flet x_1 :_{q₁}A_1 = t₁  …  x_n :_{q_n}A_n = t_n  \fin u : C}\text{let}

\inferrule{Γ ⊢  t : A \\ \text {$π$ fresh for $Γ$}}
          {Γ ⊢ λπ. t : ∀π. A}\text{w.abs}

\inferrule{Γ ⊢ t :  ∀π. A}
          {Γ ⊢ t p  :  A[p/π]}\text{w.app}
\end{mathpar}
\end{definition}

In the variable rule, one may ignore an arbitrary context $ωΓ$ ---
indeed it is acceptable not to consume $ω$-weighted variables.

The application rule may also deserve some commentary. In order to be able
to all $t$ once, one needs to produce a quantity $q$ of $A$. Thus we
split the context into a $Γ$ part and $q$ $Δ$ parts. The $Γ$ part
feeds $t$, while each of the $Δ$ feed an instance of $u$. The other
rules follow the same pattern.

\todo{Remark: auto scaling.}

\subsection{Examples of simple programs and their types}
In order to assess the power of our language, let us consider a few
simple program and the types that they inhabit.

\paragraph{K combinator}

The lamda-calculus expression $k ≝ λx. λy. x$ can be elaborated in our system to have either the type
$A ⊸ B → A$ or $A → B → A$. However, the first type subsumes the
second one, because when we heave $ω$ times $A$, we can always call
$k$ anyway and ignore the rest of $A$'s. (In this situation, we can
also call $ω$ times $k$). The lesson learned is that when a varialbe is used
(syntactically) just once, it is always better to give it the
weight 1.

\paragraph{Second order Identity}

Similarly $a ≝ λf.λx.f x$ could inhabit all the following types:
$(A → B) → A → B$,
$(A → B) ⊸ A → B$ and
$(A ⊸ B) ⊸ A ⊸ B$.

As per the lesson learned in the previous paragraph, the first type is
dominated by the second one. However the remaining two types are
incomparable. If we want to find a most general type we need to
abstact over the weight of $A$:

\[ λf. λx. f x : (A →_ρ B) → A →_ρ B.\]
\todo{This is isn't true, strictly speaking}

\paragraph{Function composition}
The need for weight abstraction typically occurs in all higher order
functions.  In particular, function composision inhabits a wealth of
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

This solution is adequate as long as one forbids calling
\begin{code}
forkIO :: IO a -> IO ()
\end{code}

In this situation, one is allowed to call runLowLevel several times in
parallel.

Using linear types, one may instead give an explicit unique instance
of the context.

\begin{code}
type Context
initialContext ::1 Context
\end{code}

The Context type will not have any runtime representation on the
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

In practice, a top-level binding with weight $1$ will behave in way
similar to |main|, in the sense that it may raise link-time type-errors.

\subsection{Primitive arrays}
\unsure{Which version should we choose? Both?}

One of the usage of linear types is to make memory management
(semi-)explicit. As an illustration we provide two possible APIs to
manipulate randomly addressable memory regions (so called ``byte arrays'' in GHC
parlance). We also propose a possible implementation strategy for the
primitives, and argue briefly for correctness.

\subsubsection{Version 1}


\begin{code}
newByteArray :: Int → (MutableByteArray ⊸ Bang k) ⊸ k
updateByteArray :: Int -> Byte → MutableByteArray ⊸ MutableByteArray
freeByteArray :: MutableByteArray ⊸ ()
freezeByteArray :: MutableByteArray ⊸ Bang ByteArray
indexMutByteArray :: Int -> MutableByteArray ⊸ (MutableByteArray ⊗ Byte)
indexByteArray :: Int -> ByteArray ⊸ (ByteArray ⊗ Byte)
\end{code}

The key primitive in the above API is |newByteArray|, whose first
argument is a size. It takes a continuation where \emph{one} reference
to the byte array is available. The continuation needs to produce a
|Bang| type. This type ensures that the continuation cannot return a
reference to the byte array.  Indeed, it is impossible to transform a
1-weighted object into an ω-weighted one without copying it
explicitly. Not returning the byte array is critical, because the
|newByteArray| function may be called $ω$ times; in which case the
result will be shared.

Other remark: the type system ensures that we never have a variable

|x : _ ω MutableByteArray|

at any point.

\subsubsection{Version 2}

\begin{code}
newByteArray :: Heap s ⊸ Int → (MutableByteArray s ⊗ Heap s)
updateByteArray :: Int -> Byte → MutableByteArray s ⊸ MutableByteArray s
freeByteArray :: MutableByteArray s ⊸ Heap s ⊸ Heap s
freezeByteArray :: MutableByteArray s ⊸ Heap s ⊸ (Heap s ⊗ Bang ByteArray)
withAHeap :: forall a. (forall s. Heap s ⊸ (Heap s ⊗ Bang a)) ⊸ a
\end{code}

\subsection{Fusion}
\label{sec:fusion}

\section{Dynamics}
\label{sec:orgheadline16}

The semantics given in this section demonstrate a further extension of
Haskell enabled by linear types: prompt deallocation of thunks. Such
an extension of the run-time system is not necessary to benefit from
linear types as was demonstrated in~\label{sec:ghc}. However, this
dynamic semantics can also help give confidence in the correctness of
the extensions of~\label{sec:ghc}.

Concretely, show that it is possible to allocate linear objects on a
heap which is not under GC, and correspondly deallocate them upon
(lazy) evaluation. To do so we present an extension of the semantics
of \textcite{launchbury_natural_1993} to our language.  As Launchbury,
we first transform terms, so that the values that are potentially
shared are bound to variables.

\begin{definition}
\begin{align*}
(λ(x:_qA). t)^* &= λ(x:_qA). (t)^* \\
x^*       &= x \\
  (t_q  x )^* &= (t)^*_q  x \\
  (t_q  u )^* &= \flet y =_{q} (u)^* \fin (t)^*_q  y \\
c_k  t₁ … t_n &= \flet x₁ =_{q_1} (t₁)^*,…, x_n =_{q_n} (t_n)^* \fin c_k x₁ … x_n \\
(\case t {c_k  x₁ … x_{n_k} → u_k})^* &= \case {(t)^*} {c_k  x₁ … x_{n_k} → (u_k)^*} \\
(\flet x_1:_{q₁}A_1= t₁  …  x_n :_{q_n}A_n = t_n \fin u)^* & = \flet x₁:_{q₁}A_1 = (t₁)^*,…, x_n:_{q_n} A_1 (t_n)^* \fin (u)^*
\end{align*}
\end{definition}

Compared to Launchbury:

\begin{itemize}
\item The heap is annotated with weights. Variables with weight $ω$
  point to the the GC heap, while variables with weight $1$ point to
  the linear heap.
\item We add a weight in the reduction relation, corresponding to the
  quantity of values to produce.
\item The rules for \emph{variable} and \emph{let} are changed to
  account for weights.
\end{itemize}

The weight in the reduction relation is used to interpret $\flet =1 …$
bindings into allocations on the proper heap.  Indeed, in $ω$ contexts,
$\flet =1 …$ must allocate on the GC heap, not on the linear
one. Indeed, consider the example:

\begin{code}
let f = _ omega (\y : _ 1 () -> case y of () -> let z = _ 1 True in z) in
let a = _ rho f ()
\end{code}

The function \texttt{f} creates some data. When run in a linear context, \texttt{f}
allocates \texttt{f} on the linear heap. When run in an unrestricted context, it
must allocate \texttt{z} on the GC heap. So, its behavior depends the value of ρ.

\begin{mathpar}
\inferrule{ }{Γ : λπ. t ⇓_ρ Γ : λπ. t}\text{w.abs}


\inferrule{Γ : e ⇓_ρ Δ : λπ.e' \\  Δ : e'[q/π] ⇓_{ρ} Θ : z}
          {Γ : e q ⇓_ρ Θ : z} \text{w.app}

\inferrule{ }{Γ : λx. e ⇓_ρ Γ : λx. e}\text{abs}


\inferrule{Γ : e ⇓_ρ Δ : λy.e' \\  Δ : e'[x/y] ⇓_{qρ} Θ : z}
           {Γ : e_q x ⇓_ρ Θ : z} \text{application}

\inferrule{Γ : e  ⇓_ω  Δ : z}{(Γ,x ↦_ω e) : x ⇓_ρ (Δ;x ↦_ω z) : z}\text{shared variable}


\inferrule{Γ : e ⇓_1 Δ : z}
{(Γ,x ↦_1 e) : x ⇓_1 Δ : z}\text{linear variable}


\inferrule{(Γ,x_1 ↦_{q_1ρ} e_1,…,x_n ↦_{q_nρ} e_n) : e ⇓_ρ Δ : z}
{Γ : \flet x₁ =_{q₁} e₁ … x_n =_{q_n} e_n \fin e ⇓_ρ Δ : z}\text{let}

\inferrule{ }{Γ : c  x₁ … x_n ⇓_ρ Γ : c  x₁ … x_n}\text{constructor}


\inferrule{Γ: e ⇓_ρ Δ : c_k  x₁ … x_n \\   Δ :  e_k[xᵢ/yᵢ] ⇓_ρ Θ :  z}
   {Γ :  \case e {c_k  y₁ … y_n ↦ e_k } ⇓_ρ Θ :  z}\text{case}
\end{mathpar}

Remark: the \emph{unrestricted variable} rule also triggers when the
weight is 1, thus effectively allowing linear variables to look on the
GC heap. This behavior allows an occurrence of a linear variable to
work in an unrestricted contexts, in turn justifying the $1 + ω = ω$
rule.

\paragraph{Theorem: The GC heap contains no references to the linear heap}
(This result is critical for heap consistency.)

Lemmas:
\begin{itemize}
\item If the weight is ω, then the linear heap is empty.
%  A
% consequence of this is that we should have main ::1 IO () --
% otherwise it's impossible to have anything in the linear heap.

% Furthermore, in order to use IO in any reasonable way, we need a
% 'linear do notation'.
\item Every variable which is bound in the linear heap is statically
  bound with weight 1.
\item Corollary: every variable bound statically with weight ω is
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
example where ||x|| is in the non-GC heap while |y| is in the
GC-heap and points to |x|:
\begin{code}
data () = ()

let x =_1 ()
let y =_ω ( case x of { () -> () })
in ()
\end{code}
However, while |()| can indeed be typed as $⊢ () :_ω ()$, the
typing rule for 'case' gives the same weight to the case-expression as
a whole as to the scrutinee (|x| in this case). Therefore
|case x of { () -> ()}| has weight 1.

Remark: for a program to turn a 1-weight into an ω-weight, one may use
the following definition:
\begin{code}
data Bang A = Box ωA
\end{code}
The expression |case x of { () -> Box ()}| has type
|Bang A|, but still with weight 1.  The programming pattern described above does not apply
just to the unit type $()$, but to any data type |D|. Indeed, for such
a type we will have a function |D ⊸ Bang D| (this may be even
efficiently implemented by copying a single pointer --- for example if
we have a single array, or a notion of compact region).  Thus at any
point where we have an intermediate result comprised of data only, we
may switch to use the linear heap. In a second phase, this data may
then be moved to the GC heap and used for general consumption.

In that light, the only way to use a linear value from the GC-heap is
to force it first, and then chain computations with |case| --- for
example as follows:
\begin{code}
let x = _1 ()
case ( case x of { () -> Box () }) of {
  Box y -> ()
}
\end{code}
This still does not create a pointer from GC-heap to non-GC heap: by the
time |y| is created, the linear value |x| has been freed.

If, on the other hand, |x| had weight $ω$, then we would be in the
usual Haskell case, and the following expression does type:
\begin{code}
let x =_ω ()
let y =_ω ( case x of { () -> () } )
in ()
\end{code}

If one wants to use the linear heap 'locally', one must use CPS.

That is:

\begin{code}
doSomethingWithLinearHeap :: (A ⊸ Bang B) ⊸ A ⊸ (B → C) ⊸ C
doSomethingWithLinearHeap f x k = case f x of
  Box y -> k y

doSomethingWithLinearHeap :: Bang B ⊸ (B → C) ⊸ C
doSomethingWithLinearHeap x k = case x of
  Box y -> k y
\end{code}

\section{Comparison with other techniques}

\subsection{Linearity as a property of types vs. linearity as a property of bindings (variables)}

In several presentations (\cite{wadler_linear_1990,mazurak_lightweight_2010,morris_best_2016}
programming languages incorporate
linearity by dividing types into two kinds. A type is either linear
or unrestricted. Unrestricted types typically includes primitive types
(\texttt{Int}), and all (strictly positive) data types. Linear types
include typically resources, effects, etc.

A characteristic of this presentation is that linearity ``infects''
every type containing a linear type. Consequently, if we want to make
a pair of (say) an integer and an effect, the resulting type must be
linear. This property means that polymorphic data structure can no
longer be used ``as is'' to store linear values. Technically, one
cannot unify a type variable of unrestricted kind to a linear
type. One can escape the issue by having polymorphism over kinds;
unfortunately to get principal types one must have subtyping between
kinds and bounded polymorphism.

In contrast, we have automatic scaling of linear types to unrestricted
ones in unrestricted contexts. This feature already partially
addresses the problem of explosion of types. In order to get principal
types we need quantification over weights, and extension of the
language of weights to products and sums.

Another issue with the ``linearity in types'' presentation is that it
is awkward at addressing the problem of ``simplified memory
management'' that we aim to tackle. As we have seen, the ability to
use an intermediate linear heap rests on the ability to turn a linear
value into an unrestricted one. When linearity is captured in types,
we must have two versions of every type that we intend to move between
the heaps. Even though it is possible to provide this, it is somewhat
annoying to duplicate every primitive type. (Possibly we could
prescribe \#Int to be linear, but this may break lots of existing
programs.)

Finally, a benefit of the linearity in variables is that polymorphism
over weights is straightforward, while linearity in types require
bounded polymorphism to achieve most general types.

\subsection{Session types vs. linear types}

\Textcite{wadler_propositions_2012} provides a good explanation of
the relation between session types vs. linear types (even though the
paper contains some subtle traps --- notably the explanation of par
and tensor in LL does not match the semantics given later.). In sum,
session types classify 'live' sessions with long-lived channels, whose
type ``evolves'' over time. In contrast, linear types are well suited
to giving types to a given bit of information. One can see thus that
linear types are better suited for a language based on a lambda
calculus, while session types are better suited for languages based on
a pi-calculus and/or languages with effects. Or put another way,
it's a matter of use cases: session types are particularly well-suited
to naturally describe communication protocols, while linear types are
well suited for describing data. One is communication centric. The
other is data centric. Yet there is a simple
encoding from session types to linear types (as Wadler demonstrates).

\todo{Compare with McBride's rig.}
\todo{talk about thunk freeing themselves}
\todo{underline that two aspects are mostly independent: 1. prompt deallocation of cons cells 2. resource management with explicit free}
\todo{Operational meaning for 1. f : A → B 2. f : A ⊸ B. that is: an input with static weight 1 can have dynamic weight w}

\printbibliography
\end{document}





%  LocalWords:  FHPC Lippmeier al honda pq th FFI monadic runLowLevel
%  LocalWords:  forkIO initialContext runtime doneWithContext Primops
%  LocalWords:  deallocation Launchbury launchbury GC scrutinee
%  LocalWords:  centric
