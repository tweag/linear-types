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

\info{Remarks: adding variables with type schemes doesn't change
  inference; we don't model bidirectional type information
  propagation, which \textsc{ghc} will perform in practice, and
  without it, it may be hard to type anything, and it may add
  complications to inference.}

\newcommand{\infstate}[4]{#4 : #3 \leadsto ⟨#1,#2⟩} % constraint, usage, type, term

\begin{figure}
  \begin{mathpar}

    \inferrule{ }{Γ,x:α⊢\infstate{∅}{(x↦1)}{α}{x}}

    \inferrule
    { Γ⊢\infstate{C_u}{U_u}{τ_u}{u}\\
      Γ⊢\infstate{C_v}{U_v}{τ_v}{v}\\
      α,p\mbox{ fresh} }
    { Γ⊢\infstate{C_u∪C_v∪\{t_u = t_v →_p α\}}{C_u+p×C_v}{α}{u v} }

    \inferrule
    { Γ,x:α⊢\infstate{C}{(U,x↦π)}{τ}{u}\\
      α,p\mbox{ fresh} }
    { Γ⊢\in \infstate{C∪\{π ⩽ p\}}{U}{α →_p τ}{λx. u}}

  \end{mathpar}
  \caption{Inference rules}
  \label{fig:inference-rules}
\end{figure}

See Figure~\ref{fig:inference-rules}.

Example: composition

\vspace{1cm}

  \inferrule
  { \inferrule
    { \inferrule
      { \inferrule
        { Γ ⊢ \infstate{∅}{(f↦1)}{α_f}{f}
          \inferrule
          { Γ ⊢ \infstate{∅}{(g↦1)}{α_g}{g}\\
            Γ ⊢ \infstate{∅}{(x↦1)}{α_x}{x} }
          { Γ ⊢ \infstate{\{α_g=α_x→_p α_{g x}\}}{(g↦1,x↦p)}{α_{g x}}{g x} } }
        { Γ = f:α_f, g:α_g, x:α_x ⊢ \infstate{\{α_g=α_x→_p α_{g x},
            α_f=α_{g x}→_q α_{f(g x)}\}}{(f↦1,g↦q,x↦qp)}{α_{f(g x)}}{f (g x)} } }
      { f:α_f, g:α_g ⊢ \infstate{\{α_g=α_x→_p α_{g x},
            α_f=α_{g x}→_q α_{f(g x)}, qp⩽r \}}{(f↦1, g↦q)}{α_x→_r
            α_{f(g x)}}{λx. f (g x)} } }
    { f:α_f ⊢ \infstate{\{α_g=α_x→_p α_{g x},
            α_f=α_{g x}→_q α_{f(g x)}, qp⩽r, q⩽s \}}{(f↦1)}{α_g→_s
            α_x→_r α_{f(g x)}}{λg x. f (g x)} }
  }
  { ⊢ \infstate{\{α_g=α_x→_p α_{g x},
            α_f=α_{g x}→_q α_{f(g x)}, qp⩽r, q⩽s, 1⩽t \}}{()}{α_f →_t α_g→_s
            α_x→_r α_{f(g x)}}{λf g x. f (g x)}}

\vspace{1cm}

Why do we need to generate $π⩽ρ$ constraints at binding site, rather
than $π=ρ$ constraints? Consider $f : (a →_ω a) →_ω a$ and the
expression $f (λx. x)$. If the constraints generated by
$λ$-abstractions were equality constraints, we would have $λx. x :
b→_pb$ with $1=p$, so the expression $f (λx. x)$ would fail to
type-check as $1≠ω$. Instead, the generated constraint is $1⩽p$, $p$
is then unified to $ω$, and we are left with checking that $1⩽ω$ which
holds.

\end{document}

% Local Variables:
% ispell-local-dictionary: "british"
% End:

%  LocalWords:  scrutinee inlining desugaring desugar
