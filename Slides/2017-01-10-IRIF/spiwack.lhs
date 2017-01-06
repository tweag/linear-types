% -*- latex -*-
% Created 2016-09-15 tor 14:09
\documentclass{beamer}
%include polycode.fmt
%format .         = ". "
%format forall a         = "∀" a
%format _ (a)         = "_{" a "}"
%format ω = "\omega"
%format π = "\pi"
%format ρ = "\rho"
%subst keyword a = "\mathsf{" a "}"
\usepackage[backend=biber,citestyle=authoryear,style=alphabetic]{biblatex}
\bibliography{../../PaperTools/bibtex/jp.bib,../../local.bib}
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
\usepackage{fontspec}
\usepackage{unicode-math}
\usepackage[plain]{fancyref}
\def\frefsecname{Section}
\def\freffigname{Figure}

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

% \newtheorem{definition}{Definition}
% \newtheorem{lemma}{Lemma}

\newcommand\HaskeLL{HaskeLL}
\newcommand\calc{{\ensuremath{λ^q}}}

\author{Jean-Philippe Bernardy, Arnaud Spiwack}
\title{Retrofitting linear types}
\date{January 10, 2017}
\hypersetup{pdflang={English}}

\begin{document}

\begin{frame}
  \titlepage
\end{frame}

\begin{frame}
  \frametitle{SAGE}

  \begin{itemize}
  \item H2020 project led by Seagate
  \item Storage for very large clusters (>1 exabyte)
  \item Distributed computation as part of IO
  \item Generalised caching: disk hierarchy
  \end{itemize}
\end{frame}

\begin{frame}
  \frametitle{The problem: linear logic is intrusive}

  \begin{code}
  dup :: Bang a ⊸ a⊗a
  dup (Bang x) = (x,x)

  id :: Bang a ⊸ a
  id (Bang x) = x

  v = dup (Bang (id (Bang 42)))
\end{code}
\end{frame}

\begin{frame}
  \frametitle{The idea: two arrows}

  \begin{itemize}
  \item $A →_1 B$: linear arrow $A ⊸ B$
  \item $A →_ω B$: usual intuitionistic arrow $A → B$
  \end{itemize}

  \hfill

  Strongly inspired by:
  \begin{itemize}
  \item \textcite{ghica_bounded_2014}
  \item \textcite{mcbride_rig_2016}
  \end{itemize}
\end{frame}

\newcommand{\deemph}[1]{{\color<2->{lightgray}#1}}
\newcommand{\andemph}[1]{{\color<2->{blue}#1}}

\begin{frame}
  \frametitle{Application \& implicit promotion}

  \begin{mathpar}
    \huge
    \inferrule
    {\deemph{Γ ⊢ t} :  A →_\andemph{q} B  \\   Δ ⊢ u : A}
    {\deemph{Γ+}\andemph{q}Δ ⊢ \deemph{t} u  :  B}\text{app}
  \end{mathpar}
\end{frame}

\begin{frame}
  \frametitle{Linear $λ$-calculus}

  \begin{mathpar}
    \Large
    \inferrule{ x:_1 A ⩽ Γ}{Γ ⊢ x : A}\text{var}

    \inferrule
    {Γ, x :_{q} A  ⊢   t : B}
    {Γ ⊢ λ(x:_q A). t  :  A  →_q  B}\text{abs}

    \inferrule
    {Γ ⊢ t :  A →_q B  \\   Δ ⊢ u : A}
    {Γ+qΔ ⊢ t u  :  B}\text{app}
  \end{mathpar}
\end{frame}

\begin{frame}
  \frametitle{One semi-ring to bind them}

  Semi-ring:
  \begin{itemize}
  \item  $0$, $+$, $1$, $.$
  \item  $0,+$ commutative monoid
  \item  $1,.$ monoid
  \item  $*$ distributes over $0,+$
  \end{itemize}

  Ordered (intuition: inclusion of intervals):
  \begin{itemize}
  \item  $⩽$
  \item $+$ increasing
  \item $0⩽c ∧ a⩽b → ca⩽cb$
  \end{itemize}
\end{frame}

\begin{frame}
  \frametitle{Contexts are modules}

  Also point-wise order

\end{frame}

\begin{frame}
  \frametitle{Weight polymorphism}
\end{frame}

\begin{frame}
  \frametitle{The case of constructors}

\end{frame}

\begin{frame}
  \frametitle{Datatype!}
\end{frame}

\begin{frame}
  \frametitle{A word on linear closures}
\end{frame}

\begin{frame}
  \frametitle{Negative types}

\end{frame}

\begin{frame}
  \frametitle{Going dependent}

\end{frame}

\begin{frame}
  \printbibliography
\end{frame}

\end{document}
