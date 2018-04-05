% -*- latex -*-

\documentclass{article}

\usepackage[backend=biber,citestyle=authoryear,style=alphabetic]{biblatex}
% \usepackage{natbib}
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
\usepackage{hyperref}
\hypersetup{
    colorlinks,
    linkcolor={red!50!black},
    citecolor={blue!50!black},
    urlcolor={blue!80!black}
  }
\usepackage{mathpartir}
\usepackage{unicode-math}
\usepackage[plain]{fancyref}
\def\frefsecname{Sec.}
\def\freffigname{Fig.}
\def\frefdefname{Def.}
\def\Frefdefname{Def.}
\def\freflemname{Lemma}
\def\Freflemname{Lemma}
\def\frefthmname{Theorem}
\def\Frefthmname{Theorem}
\def\frefappendixname{Appendix}
\def\Frefappendixname{Appendix}
\def\fancyrefdeflabelprefix{def}
\frefformat{plain}{\fancyrefdeflabelprefix}{{\frefdefname}\fancyrefdefaultspacing#1}
\Frefformat{plain}{\fancyrefdeflabelprefix}{{\Frefdefname}\fancyrefdefaultspacing#1}
\def\fancyreflemlabelprefix{lem}
\frefformat{plain}{\fancyreflemlabelprefix}{{\freflemname}\fancyrefdefaultspacing#1}
\Frefformat{plain}{\fancyreflemlabelprefix}{{\Freflemname}\fancyrefdefaultspacing#1}
\def\fancyrefthmlabelprefix{thm}
\frefformat{plain}{\fancyrefthmlabelprefix}{{\frefthmname}\fancyrefdefaultspacing#1}
\Frefformat{plain}{\fancyrefthmlabelprefix}{{\Frefthmname}\fancyrefdefaultspacing#1}
\def\fancyrefappendixlabelprefix{appendix}
\frefformat{plain}{\fancyrefappendixlabelprefix}{{\frefappendixname}\fancyrefdefaultspacing#1}
\Frefformat{plain}{\fancyrefappendixlabelprefix}{{\Frefappendixname}\fancyrefdefaultspacing#1}

%% Lhs2tex

%include polycode.fmt
%format .         = ". "
%format forall a         = "∀" a
%format _ (a)         = "_{" a "}"
%format subscript (a)         = "\!\!_{" a "}"
%format ω = "\omega"
%format π = "\pi"
%format ρ = "\rho"
%format ⅋ = "\parr"
%format :-> = ":↦"
%format ->. = "⊸"
%format DataPacked = "\Conid{Data.Packed}"
%subst keyword a = "\mathsf{" a "}"
%format mediumSpace = "\hspace{0.6cm}"
%format bigSpace = "\hspace{2cm}"
%format allocT = "alloc_T"
%format freeT = "free_T"
%format copyT = "copy_T"
%format IOL = "\varid{IO}_{\varid{L}}"
%format returnIOL = "\varid{return}_{\varid{IO}_{\varid{L}}}"
%format bindIOL = "\varid{bind}_{\varid{IO}_{\varid{L}}}"
%format `bindIOL` = "~`" bindIOL "\!`\,{}~"
%format unIOL = "\varid{unIO}_{\varid{L}}"
%format forM_ = "\varid{forM}\_"
%format mapM_ = "\varid{mapM}\_"
%format WILDCARD = "\_"
%format __ = "\_"
%format ~ = "\mathop{{\kern 1pt}''}"
%format ~: = "\mathop{{\kern 1pt}''\!\!:}"
\renewcommand\Varid[1]{\mathord{\textsf{#1}}}
\renewcommand\Conid[1]{\mathord{\textsf{#1}}}
%subst keyword a = "\mathbf{" a "}"

%% /lhs2tex

\usepackage{xspace}
\newcommand{\ghc}{\textsc{ghc}\xspace}
\newcommand{\eg}{\textit{e.g.}\xspace}
\newcommand{\ie}{\textit{i.e.}\xspace}

%% Metatheory
\newcommand{\case}[3][]{\mathsf{case}_{#1} #2 \mathsf{of} \{#3\}^m_{k=1}}
\newcommand{\casebind}[4][]{\mathsf{case}_{#1} #2 \mathsf{of} #3 \{#4\}^m_{k=1}}
\newcommand{\data}{\mathsf{data} }
\newcommand{\where}{ \mathsf{where} }
\newcommand{\inl}{\mathsf{inl} }
\newcommand{\inr}{\mathsf{inr} }
\newcommand{\flet}[1][]{\mathsf{let}_{#1} }
\newcommand{\fin}{ \mathsf{in} }
\newcommand{\varid}[1]{\ensuremath{\Varid{#1}}}
\newcommand{\susp}[1]{⟦#1⟧}
\newcommand{\wildcard}{\_}

\newcommand{\substXWithU}[2]{#2/#1}
\newcommand{\substituted}[2]{#1[#2]}
\newcommand{\termsOf}[1]{\mathnormal{terms}(#1)}
\newcommand{\multiplicatedTypes}[1]{\bigotimes(#1)}
\newcommand{\ta}[2]{γ(#1)(#2)}

\newcommand{\letjoin}[2]{\mathsf{letjoin}\ {#1}\ \mathsf{in}\ #2 }
%% /Metatheory

\newcommand{\figuresection}[1]{\par \addvspace{1em} \textbf{\sf #1}}


\usepackage{xargs}
\usepackage[colorinlistoftodos,prependcaption,textsize=tiny]{todonotes}
% ^^ Need for pgfsyspdfmark apparently?
\ifx\noeditingmarks\undefined
    % \setlength{\marginparwidth}{1.2cm} % Here's a size that matches the new PACMPL format -RRN
    \newcommand{\Red}[1]{{\color{red}{#1}}}
    \newcommand{\newaudit}[1]{{\color{blue}{#1}}}
    \newcommand{\note}[1]{{\color{blue}{\begin{itemize} \item {#1} \end{itemize}}}}
    \newenvironment{alt}{\color{red}}{}

    \newcommandx{\unsure}[2][1=]{\todo[linecolor=red,backgroundcolor=red!25,bordercolor=red,#1]{#2}}
    \newcommandx{\info}[2][1=]{\todo[linecolor=green,backgroundcolor=green!25,bordercolor=green,#1]{#2}}
    \newcommandx{\change}[2][1=]{\todo[linecolor=blue,backgroundcolor=blue!25,bordercolor=blue,#1]{#2}}
    \newcommandx{\inconsistent}[2][1=]{\todo[linecolor=blue,backgroundcolor=blue!25,bordercolor=red,#1]{#2}}
    \newcommandx{\critical}[2][1=]{\todo[linecolor=blue,backgroundcolor=blue!25,bordercolor=red,#1]{#2}}
    \newcommand{\improvement}[1]{\todo[linecolor=pink,backgroundcolor=pink!25,bordercolor=pink]{#1}}
    \newcommandx{\resolved}[2][1=]{\todo[linecolor=OliveGreen,backgroundcolor=OliveGreen!25,bordercolor=OliveGreen,#1]{#2}} % use this to mark a resolved question

    \newcommandx{\rn}[1]{\todo[]{RRN: #1}} % Peanut gallery comments by Ryan.
    \newcommandx{\simon}[1]{\todo[]{SPJ: #1}}
    \newcommandx{\jp}[1]{\todo[linecolor=blue,bordercolor=blue,backgroundcolor=cyan!10]{JP: #1}{}}
    % \newcommandx{\jp}[1]{JP: #1}
    \newcommand{\manuel}[1]{\todo[linecolor=purple,bordercolor=purple,backgroundcolor=blue!10]{Manuel: #1}{}}

\else
%    \newcommand{\Red}[1]{#1}
    \newcommand{\Red}[1]{{\color{red}{#1}}}
    \newcommand{\newaudit}[1]{#1}
    \newcommand{\note}[1]{}
    \newenvironment{alt}{}{}
%    \renewcommand\todo[2]{}
    \newcommand{\unsure}[2]{}
    \newcommand{\info}[2]{}
    \newcommand{\change}[2]{}
    \newcommand{\inconsistent}[2]{}
    \newcommand{\critical}[2]{}
    \newcommand{\improvement}[1]{}
    \newcommand{\resolved}[2]{}
    \newcommand{\rn}[1]{}
    \newcommand{\simon}[1]{}
    \newcommand{\jp}[1]{}
    \newcommand{\manuel}[1]{}
\fi

% Link in bibliography interpreted as hyperlinks.
\newcommand{\HREF}[2]{\href{#1}{#2}}

% \newtheorem{definition}{Definition}
% \newtheorem{lemma}{Lemma}
\newtheorem{remark}{Remark}

\newcommand\HaskeLL{Linear Haskell\xspace{}}
\newcommand\calc{{\ensuremath{λ^q_{→}}}}
%%%%%%%%%%%%%%%%% /Author's configuration %%%%%%%%%%%%%%%%%

\begin{document}

\title{Linear Mini-Core}

\author{J.-P. Bernardy, M. Boespflug, R. Newton, S. Peyton Jones, and
  A. Spiwack}
\date{}

\maketitle

\section{Differences between Core and the \calc{}}

The goal of this note is to document the differences between \calc{},
as described in the \href{https://arxiv.org/abs/1710.09756}{Linear
  Haskell} paper, and Core, the intermediate language of \textsc{ghc}.

We shall omit, for the time being, the minor differences, such as the
absence of polymorphism on types (\calc{} focuses on polymorphism of
multiplicities), as we don't anticipate that they cause additional
issues.

\improvement{Maybe we should give a typing rule for (mutally)
  recursive lets. Despite it probably being messy.}

\improvement{Another difference which needs to be documented is join
  points. Operating hypothesis for the moment: join points should be
  typed similarly to the case binder.}

\subsection{The case-binder}

In \calc{}, the case construction has the form

$$
\case[π] t {c_k  x₁ … x_{n_k} → u_k}
$$

In Core, it has an additional binder

$$
\casebind t z {c_k  x₁ … x_{n_k} → u_k}
$$

The additional variable $z$, called the case binder, is used in a
variety of optimisation passes, and also represents variable patterns.

A proper handling of the case binder is key, in particular, to the
compilation of deep pattern matching.

A difficulty is that for linear case, the case binder cannot be used
at the same time as the variables from the pattern: it would violate
linearity. Additionally the case binder is typically used with
different multiplicities in different branches. And all these rules must
also handle the case where $π$ is chosen to be a variable $p$.

\subsection{Case branches}

Branches of a case expression, in Core, differ from the article
description of \calc{} in two ways.
\begin{description}
\item[Non-exhaustive] The left-hand-side of branches, in Core, need to be
  distinct constructors, but, contrary to \calc{}, Core doesn't
  require that the case expression be exhaustive: there may be missing
  patterns.
\item[Wildcard] The left-hand side of one of the branches can be a
  wildcard pattern, written $\wildcard$.
\end{description}

Non-exhaustive case expressions do not cause any additional problem:
a pattern-matching failure simply raises an imprecise exception as
usual. This is equivalent to having an exhaustive case expression, with
\verb+error+ as the right-hand side of the wildcard pattern.

\section{Linear Mini-Core}

\improvement{Modify syntax to put the $π$ on the column.}

\subsection{Syntax}
\newcommand{\pip}{\kern 1.18em || }
\label{sec:syntax}

The syntax is modified to include case binders. See
\fref{fig:syntax}.

\begin{figure}
  \begin{minipage}{0.4 \textwidth} \centering
  \figuresection{Multiplicities}
  \begin{align*}
    π,μ &::= 1 ~||~ ω ~||~ p ~||~ π+μ ~||~ π·μ
  \end{align*}
  \end{minipage}
\\[3mm]
  \begin{minipage}{0.4 \textwidth} \centering
  \figuresection{Types}
  \begin{align*}
  A,B ::= A →_π B ~||~  ∀p. A ~||~ D~p_1~…~p_n
  \end{align*}
  \end{minipage}
\\[3mm]
  \begin{minipage}{0.3 \textwidth} \centering
  \figuresection{Contexts}
  \begin{align*}
    Γ,Δ & ::=  (x :_{μ} A), Γ ~||~ –
  \end{align*}
  \end{minipage}
\\[3mm]
  \begin{minipage}{0.6\linewidth} \centering
    \figuresection{Datatype declaration}
    \begin{align*}
      \data D~p_1~…~p_n~\mathsf{where} \left(c_k : A₁ →_{π₁} …    A_{n_k} →_{π_{n_k}} D\right)^m_{k=1}
    \end{align*}
  \end{minipage}

  \figuresection{Case alternatives}
  \begin{align*}
    b & ::= & c  x₁ … x_n → u
      & \pip \wildcard → u
  \end{align*}

  \figuresection{Terms}
  \begin{align*}
    e,s,t,u & ::= x & \text{variable} \\
            & \pip λ_π (x{:}A). t & \text{abstraction} \\
            & \pip t s & \text{application} \\
            & \pip λp. t & \text{multiplicity abstraction} \\
            & \pip t π & \text{multiplicity application} \\
            & \pip c t₁ … t_n & \text{data construction} \\
            & \pip \casebind[π] t z {b_k}  & \text{case} \\
            & \pip \flet[π] x_1 : A₁ = t₁ … x_n : A_n = t_n \fin u & \text{let}
  \end{align*}

  \caption{Syntax of \calc{}}
  \label{fig:syntax}
  \label{fig:contexts}
\end{figure}

\subsection{Static Semantics}
\label{sec:typing-contexts}

See \fref{fig:typing}.

\paragraph{Typing case alternatives}

The meaning of a case expression with multiplicity $π$ is that
consuming the resulting value of the case expression exactly once,
will consume the scrutinee with multiplicity $π$ (that is: exactly
once if $π=1$ and without any restriction if $π=ω$). This is the $π$
in $⊢_π^σ$ in the alternative typing judgement.

To consume the scrutiny with multiplicity $π$, we must, by definition,
consume every field $x$, whose multiplicity, as a field, is $μ$, with
multiplicity $πμ$.

This is where the story ends in \calc{}. But, in Linear Core, we can
also use the case binder. Every time the case binder $z$ (which stands
for the scrutinee) is consumed once, we consume, implicitly, $x$ with
multiplicity $μ$. Therefore the multiplicity of $x$ plus $μ$ times the
multiplicity of $z$ must equal $πμ$. Which is what $ρ+νμ = πμ$ stands
for in the rule.

There is one such constraint per field. And, since $μ$ can be
parametric, a substitution $σ$ is applied.

Note: if the constructor $c$ has no field, then we're always good; the
tag of the constructor is forced, and thus it does not matter how many
times we use $z$.\improvement{We may try and make the argument in this note
  clearer, but I don't have an idea for the moment}

\improvement{Define multiplicity equality as a judgement.}

\paragraph{Typing Join Points}

A program which starts its life as linear may be transformed by the
optimiser to use a join point. In this example, both |p| and |q| are
used linearly.

\begin{code}
  case y of y'
  { A -> p-q
  ; B -> p+q
  ; C -> p+q
  ; D -> p*q }
\end{code}

After the join point |p+q| is identified, are |p| and |q| still used linearly?
We want to answer affirmatively so that this transformation is still valid
for linear bindings.

\begin{code}
join j = p+q in
  case y of y'
  { A -> p-q
  ; B -> j
  ; C -> j
  ; D -> p*q }
\end{code}

As such, we type join bindings differently to normal let bindings. The join
variable |j| is not given an explicit multiplicity. When we see an occurence of
|j| we instead use the multiplicities of |j|s RHS in order to decide the linearity
of the variables. It is as if we inline |j| into each call site.
In this example, as |p| and |q| are both used linearly in |j|, we create
the substitution $\{ p \mapsto 1; q \mapsto 1 \}$. Then when |j| is used
in the branches we use this substituion to report the linearity of |p| and |q|
as necessary.





%%% typing rule macros %%%
\newcommand{\apprule}{\inferrule{Γ ⊢ t :  A →_π B  \\   Δ ⊢ u : A}{Γ+πΔ ⊢ t u  :  B}\text{app}}
\newcommand{\varrule}{\inferrule{ }{ωΓ + x :_1 A ⊢ x : A}\text{var}}
\newcommand{\caserule}{\inferrule{Γ   ⊢  t  : D~π_1~…~π_n \\
      σ = \substXWithU{p₁}{π₁}, … , \substXWithU{p_n}{π_n} \\
      \text{$Δ;z;D p_1…p_n ⊢_π^σ b_k : C$ for each $1 ⩽ k ⩽ m$}}
    {πΓ+Δ ⊢ \casebind[π] t z {b_k} : C}\text{case}}
%%% /macros %%%

\begin{figure}
  \begin{mathpar}
    \varrule

    \inferrule{Γ, x :_{π} A  ⊢   t : B}
    {Γ ⊢ λ_π (x{:}A). t  :  A  →_π  B}\text{abs}

    \apprule

    \inferrule{Δ_i ⊢ t_i : A_i \\ \text {$c : A_1 →_{μ_1} … →_{μ_{n-1}}
        A_n →_{μ_n} D~p_1~…~p_n$ constructor}\\
        σ = \substXWithU{p₁}{π₁}, … , \substXWithU{p_n}{π_n}}
    {ωΓ+\sum_i \substituted{μ_i}{σ}Δ_i ⊢ c  t₁ … t_n : D~π₁~…~π_n}\text{con}

    \caserule

    \inferrule{Γ_i   ⊢  t_i  : A_i  \\ Δ, x₁:_{π} A₁ …  x_n:_{π} A_n ⊢ u : C }
    { Δ+π\sum_i Γ_i ⊢ \flet[π] x_1 : A_1 = t₁  …  x_n : A_n = t_n  \fin u : C}\text{let}

    \inferrule{Γ ⊢  t : A \\ \text {$p$ fresh for $Γ$}}
    {Γ ⊢ λp. t : ∀p. A}\text{m.abs}

    \inferrule{Γ ⊢ t :  ∀p. A}
    {Γ ⊢ t π  :  \substituted{A}{\substXWithU{p}{π}}}\text{m.app}

    \inferrule{
      \text {$c : A_1 →_{μ_1} … →_{μ_{r-1}} A_n →_{μ_n} D~p_1~…~p_r$ constructor}\\
      Δ, z:_{ν} \substituted{(D p_1…p_n)}{σ}, x₁:_{ρ_1} A_i, …, x_{n}:_{ρ_{n}} A_{n} ⊢ u : C \\
      ρ_1+ν\substituted{μ_1}{σ}=π\substituted{μ_1}{σ}\quad…\quad ρ_{n}+ν\substituted{μ_{n}}{σ}=π\substituted{μ_{n}}{σ}
    }{Γ;z;D p_1…p_r ⊢_π^σ c  x₁ … x_{n} → u : C}\text{alt.constructor}

    \inferrule{
      Δ, z:_{π} \substituted{(D p_1…p_n)}{σ} ⊢ u : C
    }{Γ;z;D p_1…p_n ⊢_π^σ \wildcard → u : C}\text{alt.wildcard}
  \end{mathpar}

  \caption{Typing rules.}

  \label{fig:typing}
\end{figure}

\section{Examples}
\improvement{Explain wildcard rule in English in Sec 2.2. And adapt
  example explanation.}
\subsection{Equations}

Take, as an example, the following Linear Haskell function:
\begin{code}
data Colour = { Red; Green; Blue }

f :: Colour ->. Colour ->. Colour
f  Red   q      = q
f  p     Green  = p
f  Blue  q      = q
\end{code}
This is compiled in Core as
\begin{code}
f = \ (p ::(~One) Colour) (q ::(~One) Colour) ->
  case p of (p2 ::(~One) Colour)
  { Red       -> q
  ; WILDCARD  ->
      case q of (q2 ::(~One) Colour)
      { Green     -> p2
      ; WILDCARD  ->
          case p2 of (p3 ::(~One) Colour) { Blue -> q2 }
  }}
\end{code}
This is well typed because (focusing on the case of \verb+p2+)
\begin{itemize}
\item In the \verb+Red+ branch, no variables are introduced by the
  constructor.
\item In the \verb+WILDCARD+ branch, we see \verb+WILDCARD+ as a
  variable which can't be referenced, from the rules we get that the
  multiplicity of \verb+WILDCARD+ (necessarily $0$) plus the
  multiplicity of \verb+p2+ must be $1$. Which is the case as $p2$ is
  used linearly in each branch.
\end{itemize}

This example illustrates that, even in a multi-argument equation
setting, the compiled code is linear when all the equations,
individually, are linear.

\subsection{Unrestricted fields}

The following is well-typed:
\begin{code}
data Foo where
  Foo :: A ->. B -> C

f = \ (x ::(~One) Foo) ->
  case x of (z ::(~One) Foo)
  { Foo a b -> (z, b) }
\end{code}
It is well typed because
\begin{itemize}
\item $a$ is a linear field, hence imposes that the multiplicity of
  $a$ (here $0$) and the multiplicity of the case binder $z$
  (here $1$) sum to $1$, which holds
\item $b$ is an unrestricted field, hence imposes that the
  multiplicity of $b$ ($1$) plus $ω$ times the multiplicity of $z$
  ($1$) equals $ω$ (times $1$ since this is a linear case). That is
  $1+ω1=ω$ which holds.
\end{itemize}

\subsection{Wildcard}

The following is ill-typed
\begin{code}
f = \ (x ::(~One) Foo) ->
  case(1) x of z
  { WILDCARD -> True }
\end{code}
Because the multiplicity of \verb+WILDCARD+ (necessarily $0$) plus the
multiplicity of the case binder $z$ ($0$) does not equal $1$.

This follows intuition as $x$ really isn't being consumed ($x$ is forced
to head normal form, but if it has subfield they will never get
normalised, hence this program is rightly rejected).

This also follows our intended semantics, as $f$ amounts to
duplicating a value of an arbitrary type, which is not possible in
general.

\subsection{Duplication}

The following is ill-typed
\begin{code}
data Foo = Foo A

f = \ (x ::(~One) Foo) ->
  case(1) x of z
  { Foo a -> (z, a) }
\end{code}
Because both $z$ and $a$ are used in the branch, hence their
multiplicities sum to $ω$, but it should be $1$.

\section{Typechecking linear Mini-Core}

\newcommand{\type}[1]{\mathsf{type}(#1)}
\newcommand{\mult}[1]{\mathsf{mult}(#1)}
\newcommand{\typeof}[1]{\mathsf{lint}(#1)}

It may appear that typechecking the case rule requires guessing
multiplicities $ν$ and $ρ_i$ so that they verify the appropriate
constraint given from the context. But it is in fact not the case as
the multiplicity will be an output of the type-checker.

In this section we shall sketch how type-checking can be performed on
Linear Core.

\subsection{Representation}

Core, in \textsc{ghc}, attaches its type to every variable $x$ (let's call
it $\type{x}$). Similarly, in Linear Core, variables come with a
multiplicity ($\mult{x}$).

\begin{itemize}
\item $λ_π x : A. u$ is represented as $λ x. u$ such that $\type{x}=A$
  and $\mult{x} = π$
\item $\casebind[π] u z {…}$ is represented as
  $\casebind u z {…}$ such that $\mult{z}=π$
\end{itemize}

Contrary to $\type{x}$, which is used both at binding and call sites,
$\mult{x}$ will only be used at binding site.

\subsection{Terminology \& notations}

A mapping is a finite-support partial function.\improvement{Explain
  sum, scaling, and join for mapping.}
\begin{itemize}
\item We write $k ↦ v$ for the mapping defined only on $k$, with value
  $v$.
\item For two mapping $m₁$ and $m₂$ \emph{with disjoint supports}, we
  write $m₁,m₂$ for the mapping defined the obvious way on the union
  of their supports.
\end{itemize}


\subsection{Algorithm sketch}

The typechecking algorithm, $\typeof{t}$, takes as an input a Linear
Core term $t$, and returns a pair of
\begin{itemize}
\item The type of the term
\item A mapping of every variable to its number of usages ($ρ$). Later on we check that usages are compatible with the declared multiplicity $π$. ($ρ ⩽ π$)
\end{itemize}

We assume that the variables are properly $α$-renamed, so that there
is no variable shadowing.

The algorithm is as follows (main cases only):\improvement{Explain multiplicity
  ordering. Explain how zero-usage is handled. Explain how empty cases
  are handled.}
\begin{itemize}
\item $\typeof{x} = (\type{x}, x ↦ 1)$
\item $\typeof{u v} = (B, m_u + πm_v)$ where
  $(A →_π B, m_u)=\typeof{u}$ and $(A, m_v)=\typeof{v}$
\item $\typeof{λ_π x : A. u}=(A →_π B, m)$ where $(B, (x ↦ ρ, m)) =
  \typeof{u}$ and $ρ ⩽ π$.
\item $\typeof{\casebind[π] u z {c_k  x₁ … x_{n_k} →
      v_k}}=(A,πm_u + ⋁_{k=1}^m m_k)$, where the $c_k : B_1^k
  →_{μ_1^k} … B_{n_k}→_{μ_{n_k}^k} → D$\jp{syntax error in this type} are constructors of
  the data type $D$, $(m_u, D) = \typeof{u}$, $(A, (z ↦ ν^k, x_1 ↦
  ρ_1^k, …, {ρ}_{n_k}^k, m_k)) = \typeof{v_k}$ and $ρ_i^k+ν^kμ_i^k ⩽
  πμ_i^k$ for all $i$ and $k$.\jp{brain explodes, what about giving
    one or two special cases for $c_k$ types?}
\end{itemize}

\subsubsection{Join Rec}
The proposed core linting rules to real with joinrec and them modified variable
rule is as follows (as proposed by JP and just transcribed from the email).

There are two contexts. $\Gamma$ is the normal mapping from variables to types
whilst $\gamma$ maps join variables to a substitution. In the letjoin rule,
we type the body of the let after extending $\gamma$ with the multiplicities of
the body of the join variable.

Then we also modify the variable rule in order to obey the substitution.


\begin{mathpar}
    \inferrule{\gamma \Gamma, (x \sim \delta): A \vdash t : B \\ \delta \Gamma \vdash u : A}
              { \gamma \Gamma \vdash \letjoin{x : A = u}{t : B}} \\

    \inferrule{\delta(x) \subseteq \gamma(x)}
              {\gamma\Gamma, (x \sim \delta) : A \vdash x : A }
\end{mathpar}




\end{document}

% Local Variables:
% ispell-local-dictionary: "british"
% End:

%  LocalWords:  scrutinee
