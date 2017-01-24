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
%format ⅋ = "\parr"
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
\usepackage{cmll}
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

  \newcommand{\logoheight}{1cm}
  \newcommand{\logospacing}{\quad}
  \logo{
    \raisebox{-5mm}{\includegraphics[height=1.3\logoheight]{tweag-logo.png}}
    \logospacing
    \raisebox{-3mm}{\includegraphics[height=1.2\logoheight]{seagate-logo.png}}
    \logospacing
    \includegraphics[height=\logoheight]{SAGE-logo.png}
  }
  \center\insertlogo
\end{frame}

\begin{frame}
  \frametitle{SAGE}

  \begin{itemize}
  \item H2020 project led by Seagate
  \item Storage for very large clusters (>1 exabyte)
  \item Distributed computation as part of IO
  \item Generalised caching: disk hierarchy
  \item …
  \end{itemize}
\end{frame}

\begin{frame}
  \frametitle{The problem: linear logic is intrusive}

\begin{code}
  dup :: Bang a ⊸ a⊗a
  dup (Bang x) = (x,x)
\end{code}

\begin{code}
  id :: Bang a ⊸ a
  id (Bang x) = x
\end{code}

\begin{code}
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
  \frametitle{The linearity semi-ring}

  $\{0,1,ω\}$
  \begin{itemize}
  \item $1+1=ω$
  \item $1+ω=ω$
  \item $ω+ω=ω$
  \end{itemize}
  \begin{itemize}
  \item $ωω=ω$
  \end{itemize}
  \begin{itemize}
  \item $0⩽ω$
  \item $1⩽ω$
  \item $0\not\leqslant 1$
  \end{itemize}

\end{frame}

\begin{frame}
  \frametitle{Contexts as a module}
  \begin{block}{Module of contexts}
    \begin{itemize}
    \item $x:_pA,Γ + x:_qA,Δ ≜ x:_{p+q}A,Γ+Δ$
    \item $q(x:_pA,Γ) ≜ x:_{qp}A, qΓ$
    \end{itemize}
  \end{block}

  \hfill

  \begin{block}{Ordering of contexts}
    $x:_pA,Γ ⩽ x:_qA,Δ ⟺ p⩽q ∧ Γ⩽Δ$
  \end{block}

\end{frame}

\begin{frame}
  \frametitle{Multiplicity polymorphism}

  \begin{block}{Extend the semi-ring}
  Symbolic multiplicity expressions
    \begin{itemize}
    \item $A →_{qπ} B$
    \end{itemize}
  \end{block}
\end{frame}

\begin{frame}
  \frametitle{The case of constructors}

  \begin{block}{Constructors}
    $$
      \data D \where \left(C_k :: a_1 ⊸_{p_1} … a_n ⊸ _{p_n} b\right)^m_{k=1}
    $$
  \end{block}

  \hfill

  \begin{block}{Matching}
    $$
    \case[q]{d}{C_k x_1 … x_h → u_k}
    $$
    \begin{itemize}
    \item With $x_i$ of multiplicity $qp_i$
      \begin{itemize}
      \item Unlike linear logic
      \item Let's talk about why
      \end{itemize}
    \end{itemize}

  \end{block}
\end{frame}

\begin{frame}
  \frametitle{Datatype!}

  \begin{block}{Exponential ($!$) modality as a data type:}
    \begin{code}
      data Bang a = Bang :: a → Bang a
    \end{code}
  \end{block}

  \hfill

  \begin{block}{Exercise}
    \begin{onlyenv}<1>
      \begin{code}
        f ::  Bool   ⊸ Bang Bool
        f     True   = Bang True
        f     False  = Bang False
      \end{code}
    \end{onlyenv}
    \begin{onlyenv}<2>
      \begin{code}
        move ::  Bool   ⊸ Bang Bool
        move     True   = Bang True
        move     False  = Bang False
      \end{code}
    \end{onlyenv}
  \end{block}
\end{frame}

\begin{frame}
  \frametitle{Case?}

  \begin{block}{Duplication for Bang}
    \begin{code}
      dup ::  Bang a    ⊸ (Bang a,Bang a)
      dup     (Bang x)  = (Bang x,Bang x)
    \end{code}
  \end{block}
\end{frame}

\begin{frame}
  \frametitle{A word on linear closures}

  \begin{alertblock}{Incorrect}
    \begin{code}
      let x :: _ 1 Bool = ...
      in Bang (move x)
    \end{code}
  \end{alertblock}

  \begin{exampleblock}<2->{Correct}
    \begin{code}
      let x :: _ 1 Bool = ...
      in case (move x) of
           Bang x' -> Bang (Bang x')
    \end{code}
  \end{exampleblock}

\end{frame}

\begin{frame}
  \frametitle{Negative types}

  Encoded:
  \begin{itemize}
  \item |a & b| $≜$ |((a⊸⊥)⊕(b⊸⊥))⊸⊥|
  \item |a ⅋ b| $≜$ |((a⊸⊥)⊗(b⊸⊥))⊸⊥|
  \end{itemize}

  \hfill

  \begin{exampleblock}{Functions}
    \begin{code}
      fun2Par :: (a⊸b) ⊸ (a ⊗ (b⊸⊥)) ⊸ ⊥
      fun2Par f (a,k) = k (f a)
    \end{code}
  \end{exampleblock}

\end{frame}

\begin{frame}
  \frametitle{What's in a $⊥$?}

  $⊥$ is for effects
  \begin{itemize}
  \item \emph{e.g.} |IO ()|
  \end{itemize}

  \hfill

  Usually $⊥$ a monoid:
  \begin{itemize}
  \item |nop :: ⊥|
  \item |(;) :: ⊥ ⊸ ⊥ ⊸ ⊥|
  \end{itemize}

  \hfill

  Mix rules:
  $$
  \inferrule{\phantom{⊢Γ} \\ \phantom{⊢Δ}}{⊢}
  $$
  $$
  \inferrule{⊢Γ \\ ⊢Δ}{⊢ Γ,Δ}
  $$
\end{frame}

\begin{frame}
  \frametitle{Thoughts about implementation}

  Built-in bidirectionality:
  \begin{itemize}
  \item Typing context come in
  \item Multiplicity goes out
  \end{itemize}

  \hfill

  Integrates well in GHC
  \begin{itemize}
  \item Already somehow bidirectional
  \end{itemize}
\end{frame}

\begin{frame}
  \frametitle{Going dependent}

  \begin{itemize}
  \item Multiplicity $0$: static values.
  \end{itemize}

  \hfill

  \begin{exampleblock}{Equality}
    $$
    \inferrule{Δ⊢a:A \\ Ξ⊢b:A}{ωΓ+0Δ+0Ξ ⊢ a =_A b : ⋆}
    $$
  \end{exampleblock}

\end{frame}

\begin{frame}
  \Huge\center
  The end
\end{frame}

\begin{frame}
  \printbibliography
\end{frame}

\end{document}
