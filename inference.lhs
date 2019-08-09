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
\newcommand{\ite}[3]{\mathsf{if} {#1} \mathsf{then} #2 \mathsf{else} #3}
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

\newcommand{\letjoin}[2]{\mathsf{join}\ {#1}\ \mathsf{in}\ #2 }
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

\title{Linear type inference}

\author{J.-P. Bernardy, M. Boespflug, R. Newton, S. Peyton Jones, and
  A. Spiwack}
\date{}

\maketitle

\section{Syntax}

\section{Type inference}

Principle: \emph{multiplicity parametric\footnote{there is of coure a form of inclusion polymorphism going on when inferring ω}
  polymorphism is always declared, never inferred.}

\info{Remarks: adding variables with type
  schemes doesn't change inference; the algorithm is bidirectional we
  use $u:τ$ for inference and $u⇐τ$ for checking.}
\jp{I do not understand the first
    remark. Are we talking about multiplicity variables? (Guessing
    not?) What objection is this ``remark'' replying to?}

The general idea is to count the number of occurences of each variable
and add appropriate constraints at the binding site. Consequently we
do not in fact put the bindings mutiplicity of a variable in Γ. The
maps from variable names to multiplicities are ranged by
$U$. Constraint sets are ranged by $C$

Constraints can in general be equalities or inequalities --- equality
constraints can come from type unification.

\newcommand{\infstate}[4]{#4 : #3 \leadsto ⟨#1,#2⟩} % constraint, usage, type, term
\newcommand{\checkstate}[4]{#4 ⇐ #3 \leadsto ⟨#1,#2⟩} % constraint, usage, type, term

\begin{figure}
  \begin{mathpar}

    \inferrule{ }{Γ,x:α⊢\infstate{∅}{(x↦1)}{α}{x}}

    \inferrule
    { Γ⊢\infstate{C_u}{U_u}{τ_u}{u}\\
      Γ⊢\infstate{C_v}{U_v}{τ_v}{v}\\
      α,p\mbox{ fresh} }
    { Γ⊢\infstate{C_u∪C_v∪\{τ_u = τ_v →_p α\}}{U_u+p×U_v}{α}{u v} }

    \inferrule
    { Γ,x:α⊢\infstate{C}{(U,x↦π)}{τ}{u}\\
      α,p\mbox{ fresh} }
    { Γ⊢\infstate{C∪\{π ⩽ p\}}{U}{α →_p τ}{λx. u}}

    \inferrule
    { Γ⊢\checkstate{C_b}{U_b}{\mathsf{Bool}}{b}\\
      Γ⊢\infstate{C_t}{U_t}{τ_t}{t}\\
      Γ⊢\infstate{C_e}{U_e}{τ_e}{e}
    }
    { Γ⊢\infstate{C_b∪C_t∪C_e∪\{τ_t=τ_e\}}{U_b+(U_t∨U_e)}{τ_t}{\ite{b}{t}{e}}}

    \inferrule{ }{Γ,x:α⊢\checkstate{\{α=τ\}}{(x↦1)}{τ}{x}}

    \inferrule
    { Γ⊢\infstate{C_u}{U_u}{τ_v→_π τ_r}{u}\\
      Γ⊢\checkstate{C_v}{U_v}{τ_v}{v}}
    { Γ⊢\checkstate{C_u∪C_v∪\{τ_r = τ\}}{U_u+π×U_v}{τ}{u v} }

    \inferrule
    { Γ⊢\infstate{C_u}{U_u}{τ_u}{u}\\
      Γ⊢\infstate{C_v}{U_v}{τ_v}{v}\\
      α,p\mbox{ fresh}\\ τ_u\textrm{is not of the form} t_1→p_1 t_2}
    { Γ⊢\checkstate{C_u∪C_v∪\{τ_u = τ_v →_p τ\}}{U_u+p×U_v}{τ}{u v} }

    \inferrule
    { Γ,x:τ_x⊢\checkstate{C}{(U,x↦π_x)}{τ}{u} }
    { Γ⊢\checkstate{C∪\{π_x ⩽ π\}}{U}{τ_x →_π τ}{λx. u}}

    \inferrule
    { Γ⊢\checkstate{C_b}{U_b}{\mathsf{Bool}}{b}\\
      Γ⊢\checkstate{C_t}{U_t}{τ}{t}\\
      Γ⊢\checkstate{C_e}{U_e}{τ}{e}
    }
    { Γ⊢\checkstate{C_b∪C_t∪C_e}{U_b+(U_t∨U_e)}{τ}{\ite{b}{t}{e}}}

  \end{mathpar}
  \caption{Inference rules}
  \label{fig:inference-rules}
\end{figure}

See Figure~\ref{fig:inference-rules}.

Examples are simplified by inlining syntactic unification constraint
immediately, in order to focus on the linearity constraints, and gain
horizontal space.

Example: composition\improvement{The $Γ$ is incorrect, fix! Doesn't
  benefit from bidirectionality.}

\vspace{1cm}

  \inferrule
  { \inferrule
    { \inferrule
      { \inferrule
        { Γ ⊢ \infstate{∅}{(f↦1)}{α_f}{f}
          \inferrule
          { Γ ⊢ \infstate{∅}{(g↦1)}{α_g}{g}\\
            Γ ⊢ \infstate{∅}{(x↦1)}{α_x}{x} }
          { Γ ⊢ \infstate{∅}{(g↦1,x↦p)}{α_x→_p α_{g x}}{g x} } }
        { Γ = f:α_{g x}→_q α_{f(g x)}, g:α_x→_p α_{g x}, x:α_x ⊢ \infstate{∅}{(f↦1,g↦q,x↦qp)}{α_{f(g x)}}{f (g x)} } }
      { f:α_{g x}→_q α_{f(g x)}, g:α_x→_p α_{g x} ⊢ \infstate{\{qp⩽r \}}{(f↦1, g↦q)}{α_x→_r
            α_{f(g x)}}{λx. f (g x)} } }
    { f:α_{g x}→_q α_{f(g x)} ⊢ \infstate{\{qp⩽r, q⩽s \}}{(f↦1)}{(α_x→_p α_{g x})→_s
            α_x→_r α_{f(g x)}}{λg x. f (g x)} }
  }
  { ⊢ \infstate{\{qp⩽r, q⩽s, 1⩽t \}}{()}{(α_{g x}→_q α_{f(g x)}) →_t (α_x→_p α_{g x})→_s
            α_x→_r α_{f(g x)}}{λf g x. f (g x)}}

\vspace{1cm}

Why do we need to generate $π⩽ρ$ constraints at the binding site, rather
than $π=ρ$ constraints? Consider $f : (a →_ω a) →_ω a$ and the
expression $f (λx. x)$. If the constraints generated by
$λ$-abstractions were equality constraints, we would have $λx. x :
b→_pb$ with $1=p$, so the expression $f (λx. x)$ would fail to
type-check as $1≠ω$. Instead, the generated constraint is $1⩽p$, $p$
is then unified to $ω$, and we are left with checking that $1⩽ω$, which
holds.

\subsection{Solving constraints}

(Very rough DRAFT)

At some well-chosen points, (ie. top-level bindings) GHC does
generalisation. Traditionally this can mean introducing universal
quantification in types, instead of keeping (meta)variables around.

When generalising, we won't however introduce any
multiplicity-polymorphism.  Instead all variables will be instanciated
with an expression compatible with the constraints, if such expression
exists.

More precisely, we propose the following strategy for multiplicities:
We attempt to solve (all) multiplicity constraints using a general
algorithm (see below). If they are not
solvable, then we report a type error.
If they are solvable, we have a solution $σ$\jp{Maybe should be called $U$ according to above stated convention?}.
We then check
if any meta variable $p$ appears in the generalised type
candidate. If $p$ is constrained with an equality in $σ$, we
simply set it to its value. Failing this, if a variable $p$ is
constrained from below ($π ≤ p$ exists in $σ$), we set $p$ to
$ω$. Failing this, if a variable is constrained from above ($p ≤ π$
exists in $σ$), then we set $p = π$ (potentially introducing more
metavariables to eliminate). \footnote{Consequently if $p$ is constrained from both direction it is set to $ω$.}
Failing this, $p$ is free, but we set it
to $ω$ --- no generalisation. (We could equally well set it to $1$, but using $ω$ is considered less surprising to the user.)

Doing the above assignments do not preserve the property that $σ$ is a solution.
So, when all variables are fixed, we re-check that $σ$ is still a
solution. If it isn't, then we report a type error. This type error
can potentially suggest a more general type to the user, which would
typecheck if they'd write it explicitly.


The solver algorithm would remove all constraints containing a sum expression and then run a
standard solver (AC).\jp{suitable ref for this solver?}  How to remove such constraints? The
system can introduce sums if a variable has several occurences, as in:
($π + ρ ≤ p$). In such a case we can replace the constraint by $ρ=ω$
--- if we find a solution with this new constraint, then we know that
$π + ρ ≤ p$ is also satisfied. If we don't find a solution then we can
indicate to the user that we made a simplificating assumption when
reporting the error. (In a first instance we can forbid users to write sum)

TODO: what to do if the user wrote a sum?  Unfortunately the user may
have written a sums explicitly. Perhaps in this case, if the type of
the function is available at the binding site, we can locally check
that the constraint is satisfied using heuristics.


\end{document}

% Local Variables:
% ispell-local-dictionary: "british"
% End:

%  LocalWords:  scrutinee inlining desugaring desugar
