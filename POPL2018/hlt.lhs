% -*- latex -*-

%% For double-blind review submission
\documentclass[acmsmall,10pt,review,anonymous]{acmart}
\settopmatter{printfolios=true,printacmref=false}
\def\draftmode{}

%% For single-blind review submission
% \documentclass[acmsmall,10pt,review]{acmart}\settopmatter{printfolios=true}

%% For final camera-ready submission
%% \documentclass[acmsmall,10pt]{acmart}\settopmatter{}

% TOGGLE ME to turn off all the commentary:
\InputIfFileExists{no-editing-marks}{
  \def\noeditingmarks{}
}


%% Note: Authors migrating a paper from PACMPL format to traditional
%% SIGPLAN proceedings format should change 'acmsmall' to
%% 'sigplan'.

%%%%%%%%%%%%%%%%% Author's configuration %%%%%%%%%%%%%%%%%

\usepackage[mathletters]{ucs}
\usepackage[utf8x]{inputenc}
\DeclareUnicodeCharacter{8797}{\ensuremath{\stackrel{\scriptscriptstyle {\mathrm{def}}}{=}}}
\DeclareUnicodeCharacter{183}{\ensuremath{\cdot}} % ·
%include polycode.fmt
%format .         = ". "
%format forall a         = "∀" a
%format _ (a)         = "_{" a "}"
%format ω = "\omega"
%format π = "\pi"
%format ρ = "\rho"
%format ⅋ = "\parr"
%format :-> = ":↦"
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
%format unIOL = "\varid{unIO}_{\varid{L}}"
%format forM_ = "\varid{forM}\_"
%format mapM_ = "\varid{mapM}\_"
%format __ = "\_"
\def\mathindent{1em} % used by lhs2tex for indentation of code
\renewcommand\Varid[1]{\mathord{\textsf{#1}}}
\renewcommand\Conid[1]{\mathord{\textsf{#1}}}
%subst keyword a = "\mathbf{" a "}"

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
\def\frefsecname{Sec.}
\def\freffigname{Fig.}
\def\frefdefname{Def.}
\def\Frefdefname{Def.}
\def\freflemname{Lemma}
\def\Freflemname{Lemma}
\def\frefappendixname{Appendix}
\def\Frefappendixname{Appendix}
\def\fancyrefdeflabelprefix{def}
\frefformat{plain}{\fancyrefdeflabelprefix}{{\frefdefname}\fancyrefdefaultspacing#1}
\Frefformat{plain}{\fancyrefdeflabelprefix}{{\Frefdefname}\fancyrefdefaultspacing#1}
\def\fancyreflemlabelprefix{lem}
\frefformat{plain}{\fancyreflemlabelprefix}{{\freflemname}\fancyrefdefaultspacing#1}
\Frefformat{plain}{\fancyreflemlabelprefix}{{\Freflemname}\fancyrefdefaultspacing#1}
\def\fancyrefappendixlabelprefix{appendix}
\frefformat{plain}{\fancyrefappendixlabelprefix}{{\frefappendixname}\fancyrefdefaultspacing#1}
\Frefformat{plain}{\fancyrefappendixlabelprefix}{{\Frefappendixname}\fancyrefdefaultspacing#1}

\usepackage{xspace}
\newcommand{\ghc}{\textsc{ghc}\xspace}
\newcommand{\eg}{\textit{e.g.}\xspace}
\newcommand{\ie}{\textit{i.e.}\xspace}

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


\usepackage{xargs}
\usepackage[colorinlistoftodos,prependcaption,textsize=tiny]{todonotes}
% ^^ Need for pgfsyspdfmark apparently?
\ifx\noeditingmarks\undefined    
    \setlength{\marginparwidth}{1.2cm} % Here's a size that matches the new PACMPL format -RRN
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

\newcommand\HaskeLL{Hask-\textsc{ll}\xspace{}}
\newcommand\calc{{\ensuremath{λ^q_\to}}}


%%%%%%%%%%%%%%%%% /Author's configuration %%%%%%%%%%%%%%%%%

%% Some recommended packages.
\usepackage{booktabs}   %% For formal tables:
                        %% http://ctan.org/pkg/booktabs
\usepackage{subcaption} %% For complex figures with subfigures/subcaptions
                        %% http://ctan.org/pkg/subcaption
\usepackage{wrapfig}
% \usepackage{framed}

%% Journal information (used by PACMPL format)
%% Supplied to authors by publisher for camera-ready submission
\acmJournal{PACMPL}
\acmVolume{1}
\acmNumber{1}
\acmArticle{1}
\acmYear{2017}
\acmMonth{1}
\acmDOI{10.1145/nnnnnnn.nnnnnnn}
\startPage{1}



%% Copyright information
%% Supplied to authors (based on authors' rights management selection;
%% see authors.acm.org) by publisher for camera-ready submission
\setcopyright{none}             %% For review submission
%\setcopyright{acmcopyright}
%\setcopyright{acmlicensed}
%\setcopyright{rightsretained}
%\copyrightyear{2017}           %% If different from \acmYear


%% Bibliography style
\bibliographystyle{ACM-Reference-Format}
%% Citation style
%% Note: author/year citations are required for papers published as an
%% issue of PACMPL.
\citestyle{acmauthoryear}   %% For author/year citations


\begin{document}

%% Title information
\title{Retrofitting Linear Types}       %% [Short Title] is optional;
                                        %% when present, will be used in
                                        %% header instead of Full Title.
% \titlenote{with title note}             %% \titlenote is optional;
%                                         %% can be repeated if necessary;
%                                         %% contents suppressed with 'anonymous'
% \subtitle{Subtitle}                     %% \subtitle is optional
% \subtitlenote{with subtitle note}       %% \subtitlenote is optional;
%                                         %% can be repeated if necessary;
%                                         %% contents suppressed with 'anonymous'


%% Author information
%% Contents and number of authors suppressed with 'anonymous'.
%% Each author should be introduced by \author, followed by
%% \authornote (optional), \orcid (optional), \affiliation, and
%% \email.
%% An author may have multiple affiliations and/or emails; repeat the
%% appropriate command.
%% Many elements are not rendered, but should be provided for metadata
%% extraction tools.

%% Author with single affiliation.
\author{Jean-Philippe Bernardy}
\affiliation{%
  \institution{University of Gothenburg}
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

% The default list of authors is too long for headers
\renewcommand{\shortauthors}{J.-P. Bernardy, M. Boespflug, R. Newton,
  S. Peyton Jones, and A. Spiwack}

%% Paper note
%% The \thanks command may be used to create a "paper note" ---
%% similar to a title note or an author note, but not explicitly
%% associated with a particular element.  It will appear immediately
%% above the permission/copyright statement.
% \thanks{}
%% \thanks is optional
%% can be repeated if necesary
%% contents suppressed with 'anonymous'


%% Abstract
%% Note: \begin{abstract}...\end{abstract} environment must come
%% before \maketitle command
\begin{abstract}
  Linear type systems have a long and storied history, but not a clear
  path forward to integrate with existing languages such as OCaml or
  Haskell. In this paper, we study a linear type system
  designed with two crucial properties in mind:
  backwards-compatibility and code reuse across linear and non-linear
  users of a library. Only then can the benefits of linear types
  permeate conventional functional programming.  Rather than bifurcate
  % not just data; functions must also be bifurcated due to closures.
  types into linear and non-linear counterparts, we instead
  attach linearity to {\em function arrows}.  Linear functions can
  receive inputs from linearly-bound values, but can {\em also} operate over
  unrestricted, regular values.

  To demonstrate the efficacy of our linear type system~---~both how
  easy it can be integrated in an existing language implementation and
  how streamlined it makes it to write programs with linear
  types~---~we implemented our type system in 
  \textsc{ghc}, the leading Haskell compiler, and demonstrate
  two kinds of applications of linear types:
  mutable data with pure interfaces;
%  making side-effecting functions pure instead;
 % that otherwise would be considered to have side effects, pure;
  and enforcing protocols in \textsc{i/o}-performing functions. %
  \ifx\draftmode\undefined \else \vspace{-5mm} \fi
\end{abstract}

%% \if@ACM@review
\ifx\draftmode\undefined    
%% 2012 ACM Computing Classification System (CSS) concepts
%% Generate at 'http://dl.acm.org/ccs/ccs.cfm'.
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
%% End of generated code

%% Keywords
%% comma separated list
\keywords{GHC, Haskell, laziness, linear logic, linear types,
 polymorphism, typestate}  %% \keywords is optional
\fi

%% \maketitle
%% Note: \maketitle command must come after title commands, author
%% commands, abstract environment, Computing Classification System
%% environment and commands, and keywords command.
\maketitle

\section{Introduction}
\label{sec:introduction}

Despite their obvious promise, and a huge research literature, linear
type systems have not made it into mainstream programming languages,
even though linearity has inspired uniqueness typing in Clean, and
ownership typing in Rust.  We take up this challenge by extending
Haskell with linear types.
%
Our design supports many applications for linear types, but we focus on
two particular use-cases.  First, safe
update-in-place for mutable structures, such as arrays; and second,
enforcing access protocols for external \textsc{api}s, such as files,
sockets, channels and other resources.  Our particular contributions
are these:
\begin{itemize}
\item Our extension to Haskell, dubbed \HaskeLL, is
      \emph{non-invasive}.  Existing programs continue to typecheck,
      and existing data types can be used as-is even in linear parts
      of the program.
\item The key to this non-invasiveness is that, in contrast to most other
      approaches, we focus on \emph{linarity on the function arrow}
      rather than \emph{linearity in the kinds} (\fref{sec:lin-arrow}).
\item Every function arrow can be declared linear, including those of
      constructor types. This results in data-types which can store
      both linear values, in addition to unrestricted ones (\fref{sec:data-types}).
\item A benefit of linearity-on-the-arrow is that it naturally supports
      \emph{linearity polymorphism} (\fref{sec:lin-poly}).  This contributes
      to a smooth extension of Haskell by allowing many existing functions
      (map, compose, etc) to be given more general types, so they can
      work uniformly in both linear and non-linear code.
\item We formalise our system in a small, statically-typed core
      calculus that exhibits all these features (\fref{sec:calculus}).
      It enjoys the usual properties of progress and preservation.
\item We have implemented a prototype of the system as a modest extension to \textsc{ghc}
      (\fref{sec:impl}), which substantiates our claim of non-invasiveness.
      We use this prototype to implement case-study applications (\fref{sec:applications}).
      Our prototype performs linearity \emph{inference}, but a systematic
      treatment of type inference for linearity in our system remains open.
\end{itemize}
There is a rich literature on linear type systems, as we discuss in a long
related work section (\fref{sec:related}).

\section{Motivation and intuitions}
\label{sec:programming-intro}

Informally, \emph{a function is ``linear'' if it consumes its argument exactly once}.
(It is ``affine'' if it consumes it at most once.)  A linear type system
gives a static guarantee that a claimed linear function really is linear.
There are many motivations for linear type systems, but they mostly come down
to two questions:
\begin{itemize}
\item \emph{Is it safe to update this value in-place} (\fref{sec:freezing-arrays})?
That depends on whether there
are aliases to the value; update-in-place is \textsc{ok} if there are no other pointers to it.
Linearity supports a more efficient implementation, by $O(1)$ update rather than $O(n)$ copying.
\item \emph{Am I obeying the usage protocol of this external resource}
(\fref{sec:io-protocols})?
For example, an open file should be closed, and should not be used after it it has been closed;
a socket should be opened, then bound, and only then used for reading; a malloc'd memory
block should be freed, and should not be used after that.
Here, linearity does not affect efficiency, but rather eliminates many bugs.
\end{itemize}
We introduce our extension to Haskell, which we call \HaskeLL{} (Haskell with
Linear Logic), by focusing on these two use-cases.  In doing so, we introduce a
number of ideas that we flesh out in subsequent subsections.

\subsection{Operational intuitions}
\label{sec:consumed}

We have said informally that \emph{``a linear function consumes its argument
exactly once''}. But what exactly does that mean?

\begin{quote}
\emph{Meaning of the linear arrow}:
|f :: s ⊸ t| guarantees that if |(f u)| is consumed exactly once,
then the argument |u| is consumed exactly once.
\end{quote}
To make sense of this statement we need to know what ``consumed exactly once'' means.
Our definition is based on the type of the value concerned:
\begin{definition}[Consume exactly once]~ \label{def:consume}
\begin{itemize}
\item To consume a value of atomic base type (like |Int| or |Ptr|) exactly once, just evaluate it.
\item To consume a function exactly once, apply it to one argument, and consume its result exactly once.
\item To consume a pair exactly once, pattern-match on it, and consume each component exactly once.
\item In general, to consume a value of an algebraic data type exactly once, pattter-match on it,
  and consume all its linear components exactly once
  (\fref{sec:non-linear-constructors})\footnote{You may deduce that pairs have linear components,
    and indeed they do, as we discuss in \fref{sec:non-linear-constructors}.}.
\end{itemize}
\end{definition}
\noindent
This definition is enough to allow programmers to reason about the
typing of their functions, and it drives the formal typing judgements in
\fref{sec:statics}.

Note that a linear arrow specifies \emph{how the function uses its argument}. It does not
restrict \emph{the arguments to which the function can be applied}.
In particular, a linear function cannot assume that it is given the
unique pointer to its argument.  For example, if |f :: s ⊸ t|, then\
this is fine:
\begin{code}
g :: s -> t
g x = f x
\end{code}
The type of |g| makes no particular guarantees about the way in which it uses |x|;
in particular, |g| can pass that argument to |f|.

% A consequence of this definition is that an \emph{unrestricted} value,
% \emph{i.e.} one which is not guaranteed to be used exactly once, such
% as the argument of a regular function |g :: a -> b|, can freely be
% passed to |f|: |f| offers stronger guarantees than regular
% functions. On the other hand a linear value |u|, such as the argument of
% |f|, \emph{cannot} be passed to |g|: consuming |g u| may consume |u| several
% times, or none at all, both violating the linearity guarantee that |u|
% must be consumed exactly once.
%
% In light of this definition, suppose that we have |f :: a ⊸ b| and |g
% :: b -> c|. Is |g (f x)| correct? The answer depends on the linearity
% of |x|:
% \begin{itemize}
% \item If |x| is a linear variable, \emph{i.e.} it must be consumed
%   exactly once, we can ensure that it's consumed exactly once by
%   consuming |f| exactly once: it is the definition of linear
%   functions. However, |g| does not guarantee that it will consume |f
%   x| exactly once, irrespective of how |g (f x)| is consumed. So |g (f
%   x)| cannot be well-typed.
% \item If |x| is an unrestricted variable, on the other hand, there is
%   no constraint on how |x| must be consumed. So |g (f x)| is perfectly
%   valid. And it is, indeed, well-typed. Refer to \fref{sec:statics}
%   for the details.
% \end{itemize}
%
% In the same spirit, an unrestricted value |u| can never point to a
% linear value |v|: if |u| is never consumed (which is a correct use of
% an unrestricted value), then |v| will never be consumed either, which
% is incorrect of a linear value.


\subsection{Safe mutable arrays}
\label{sec:freezing-arrays}

The Haskell language provides immutable arrays, built with the function |array|\footnote{
Haskell actually generalises over the type of array indices, but for this
paper we will assume that the arrays are indexed, from 0, by |Int| indices.}:
\begin{code}
array :: Int -> [(Int,a)] -> Array a
\end{code}

\begin{wrapfigure}[7]{r}[0pt]{7.0cm} % lines, placement, overhang, width
%\vspace{-6mm}
\begin{code}
  type MArray s a
  type Array a

  newMArray :: Int -> a -> ST s (MArray s a)
  read  :: MArray s a -> Int -> ST s a
  write :: MArray s a -> (Int, a) -> ST s ()
  unsafeFreeze :: MArray s a -> ST s (Array a)

  forM_ :: Monad m => [a] -> (a -> m ()) -> m ()
  runST :: (forall a. ST s a) -> a
\end{code}
\vspace{-4mm}
\caption{Signatures for array primitives (current \textsc{ghc})}
{\vspace{-2.5mm}\hrulefill}
\label{fig:array-sigs}
\end{wrapfigure}
%
But how is |array| implemented? A possible answer is ``it is built-in; don't ask''.
But in reality \textsc{ghc} implements |array| using more primitive pieces, so that library authors
can readily implement more complex variations --- and they certainly do: see for example \fref{sec:cursors}.  Here is the
definition of |array|, using library functions whose types are given
in \fref{fig:array-sigs}.

\begin{code}
array :: Int -> [(Int,a)] -> Array a
array size pairs = runST
  (do  { ma <- newMArray size
       ; forM_ pairs (write ma)
       ; return (unsafeFreeze ma) })
\end{code}
In the first line we allocate a mutable array, of type |MArray s a|.
Then we iterate over the |pairs|, with |forM_|, updating the array in place
for each pair.  Finally, we freeze the mutable array, returning an immutable
array as required.  All this is done in the |ST| monad, using |runST| to
securely encapsulate an imperative algorithm in a purely-functional context,
as described in \cite{launchbury_st_1995}.


Why is |unsafeFreeze| unsafe?  The result of |(unsafeArray ma)| is a new
immutable array, but to avoid an unnecessary copy,
the two are actually \emph{the same array}.  The intention is, of course, that
that |unsafeFreeze| should be the last use of the mutable array; but
nothing stops us continuing to mutate it further, with quite undefined semantics.
The ``unsafe'' in the function name is a \textsc{ghc} convention meaning ``the programmer
has a proof obligation here that the compiler cannot check''.

The other unsatisfactory thing about the monadic approach to array
construction is that it is over-sequential. Suppose you had a pair of
mutable arrays, with some updates to perform to each; these updates could
be done in {\em parallel}, but the |ST| monad would serialise them.

Linear types allow a more secure and less sequential interface.  \HaskeLL{}
introduces a new kind of function type: the \emph{linear arrow} |a⊸b|. A linear
function |f :: a⊸b| must consume its argument \emph{exactly once}.  This new
arrow is used in a new array \textsc{api}, given in
\fref{fig:linear-array-sigs}.
%
\begin{figure}[h]
\hrulefill
\vspace{-2mm}
\begin{code}
  type MArray a
  type Array a

  newMArray :: Int -> (MArray a ⊸ Unrestricted b) ⊸ b
  write :: MArray a ⊸ (Int, a) -> MArray a
  read :: MArray a ⊸ Int -> (MArray a, Unrestricted a)
  freeze :: MArray a ⊸ Unrestricted (Array a)
\end{code}
%{\vspace{-30mm}\noindent\rule{4cm}{0.4pt}\vspace{30mm}}
\vspace{-5mm}
\caption{Type signatures for array primitives (linear version), allowing
  in-place update.}
{\vspace{-2.5mm}\hrulefill\vspace{-2.5mm}}
\label{fig:linear-array-sigs}
\end{figure}

\noindent
Using this \textsc{api} we can define |array| thus:
%
\begin{code}
array :: Int -> [(Int,a)] -> Array a
array size pairs = newMArray size (\ma -> freeze (foldl write ma pairs))
\end{code}
%\noindent
There are several things to note here:
\begin{itemize}

\item The function |newMArray| allocates a fresh, mutable array of the
  specified size, and passes it to the function supplied as the second
  argument to |newMArray|, as a {\em linear} value |ma|.

\item We still disinguish the type of mutable arrays |MArray| from that of
  immutable arrays |Array|. Only immutable arrays are allowed to be non-linear
  (unrestricted).
  %% In our system, \emph{linearity is a property of function arrows,
  %%   not of types} (\fref{sec:lin-arrow}).
  The way to say that results
  can be freely shared is to use |Unrestricted| (\fref{sec:data-types}), as in the type of
  |freeze|. 

\item Because |freeze| consumes its input, there is no danger of the same
  mutable array being subsequently written to, eliminating the problem with
  |unsafeFreeze|.
  
\item Since |ma| is linear, we can only use it once. Thus each call to
  |write| returns a (logically) new array, so that the array is single-threaded,
  by |foldl|, through the sequence of writes.
  
\item Above, |foldl| has the type |(a ⊸ b ⊸ a) -> a ⊸ [b] ⊸ a|,
which expresses that it consumes its second argument linearly
(the mutable array), while the function it is given as
its first argument (|write|) must be linear.
As we shall see in \fref{sec:lin-poly} this is not a new |foldl|, but
an instance of a more general, multiplicity-polymorphic version of
a single |foldl| (where ``multiplicity'' refers to how many times a function
consumes its input).

\item Finally, in the {\sc api}, no function that consumes an |MArray a|
  returns more than a {\em single} pointer to it.  Together with the fact
  that |newMArray| introduces {\em only} linear |MArray| bindings, this ensures {\bf
    uniqueness}, which in turn allows update-in-place.
%  (Otherwise we would could retain old values of the array, and could not update-in-place.)
%  have concurrent accesses to the array, and reference-transparency would be violated.

\end{itemize}

In an application, |newMArray k|, we see the principle that \emph{linearity is a
  property of function arrows, not of types} in action (elaborated in
\fref{sec:lin-arrow}).
%
  That function |k| has the type |MArray a ⊸ Unrestricted b|. 
%  This has two consequences.  First, |k| is guaranteed to consume |ma| exactly once.
  %  In particular |k| cannot  pass |ma| to multiple functions.
  It consumes the input array once and can return a value of any
  type |Unrestricted b| it wishes, but the payload of type |b| must
  {\em not} be linear (by definition of |Unrestricted|).
  %
%%   As a consequence, in order to access that payload, |newMArray| must force the
%%   execution of |k ma| until all linear objects (including |ma|) are
%%   consumed. This forcing means: (1) it does
%%   not matter how many times the result of |newMArray k| is used;
%%   and (2) |k| needs to be called only once and thus a only single |ma| is ever
%%   needed.
%% %
%%  Second, no pointer to |ma| can escape into the control of the {\sc GC}.
  This implies that no mutable pointer to |ma| can {\em escape} when |newArray|
  returns (\ie{} when the |b| result of |newArray| is evaluated).
  
With this mutable array \textsc{api},
the |ST| monad has disappeared altogether; it is the array \emph{itself}
that must be single threaded, not the operations of a monad. That removes
the unnecessary sequentialisation we mentioned earlier, \newaudit{and creates
opportunities for purely functional parallelism.}
%
\if{0}
    In fact, {\em futures} (\ie par/pseq ~\cite{multicore-haskell}) are sufficient
    for parallel updates to |MArray|s; we don't need threads.  These work well with
    linear functions for splitting and joining array slices:

    \noindent
    %\begin{center}
    \begin{minipage}{0.55 \textwidth}  
    \hspace{-3mm}
    \begin{code}
    split :: Int -> MArray a ⊸ (MArray a, MArray a)
    \end{code}
    \end{minipage}%
    \begin{minipage}{0.45 \textwidth}
    \begin{code}
    join  :: (MArray a, MArray a) ⊸ MArray a  
    \end{code}
    \end{minipage}
    %\end{center}
\fi{}

Compared to the \textit{status quo} (using |ST| and |unsafeFreeze|), the
other major benefit
is in shrinking the trusted code base, because more library code (and it
can be particularly gnarly code) is statically typechecked.  Clients who
use only {\em immutable} arrays do not see the inner workings of the library, and will
be unaffected.  Our second use-case has a much more direct impact on library clients.
%
%% \rn{I have mixed feelings about this.  What about the client of the mutable
%%   array APIs?  Data.Vector.Mutable etc.  Also, there's the matter of safe
%%   freezing like ``create''.}

%\vspace{-1mm}
\subsection{I/O protocols} \label{sec:io-protocols}
%\vspace{-1mm}

\begin{figure}
  \vspace{-4mm}
\begin{minipage}{0.40 \textwidth} 
%  \begin{framed}   
\begin{code}
  type File
  openFile :: FilePath -> IO File
  readLine :: File -> IO ByteString
  closeFile :: File -> IO ()
\end{code}
\vspace{-7mm}
\caption{Types for traditional file IO} \label{fig:io-traditional}
%  \end{framed}
\end{minipage}%
\begin{minipage}{0.60 \textwidth}
\begin{code}
  type File
  openFile :: FilePath -> IOL 1 File
  readLine :: File a ⊸ IOL 1 (File, Unrestricted ByteString)
  closeFile :: File ⊸ IOL ω ()
\end{code}
\vspace{-7mm}
\caption{Types for linear file IO} \label{fig:io-linear}
\end{minipage}
\vspace{-2mm}
\hrulefill
\end{figure}

Consider the \textsc{api} for files in \fref{fig:io-traditional}, where a
|File| is a cursor in a physical file.
%
Each call
to |readLine| returns a |ByteString| (the line) and moves the cursor one line
forward.  But nothing stops us reading a file after we have closed it,
or forgetting to close it.
An alternative \textsc{api} using linear types is given in \fref{fig:io-linear}.
Using it we can write a simple file-handling program, |firstLine|, \Red{shown here}.
%
%\begin{wrapfigure}[7]{r}[0pt]{6.0cm} \vspace{-5mm}
\begin{code}
firstLine :: FilePath -> IOL ω Bytestring
firstLine fp =
  do  { f <- open fp
      ; (f, Unrestricted bs) <- readLine f
      ; close f
      ; return bs }
\end{code}
%\end{wrapfigure}
%
Notice several things:
\begin{itemize}

\item Operations on files remain monadic, unlike the case with mutable arrays.
I/O operations affect the world, and hence must be sequenced.  It is not enough
to sequence operations on files individually, as it was for arrays.

\item We generalise the |IO| monad so that it expresses whether or not the
returned value is linear.  We add an extra {\em multiplicity} type parameter |p| to the monad |IOL|,
where |p| can be |1| or |ω|, indicating a linear or unrestricted result, respectively.
%
Now |openFile| returns |IOL 1 (File ByteString)|,
the ``|1|'' indicating that the returned |File| must be used linearly.
We will return to how |IOL| is defined in \fref{sec:linear-io}.

\end{itemize}

% lame hack / workaround
\begin{itemize}

\item As before, operations on linear values must consume their input
and return a new one; here |readLine| consumes the |File| and produces a new one.

\item Unlike the |File|, the |ByteString| returned by |readLine| is unrestricted,
and the type of |readLine| indicates this.

\end{itemize}
It may seem tiresome to have to thread the |File| as well as sequence
operations with the |IO| monad. But in fact it is often useful do
to so, because we can use types
to witness the state of the resource, \eg, with separate
types for an open or closed |File|. We show applications in \fref{sec:cursors} and \fref{sec:sockets}.
% (which we can think of as a type-level state, or {\em typestate}~\cite{strom_typestate_1983})
% JP: who cares?
\subsection{Linear data types}
\label{sec:linear-constructors}
\label{sec:data-types}


With the above intutions in mind, what type should we assign to a data
constructor such as the pairing constructor |(,)|?  Here are two possibilities:
\begin{center}
\vspace{-1mm}
\begin{code}
 (,) ::  a ⊸ b ⊸ (a,b)   bigSpace       (,) ::  a -> b -> (a,b)
\end{code}
\vspace{-4mm}
\end{center}
Using the definition in \fref{sec:consumed}, the former is clearly the correct
choice: if the result of |(,) e1 e2| is consumed exactly once,
then (by \fref{def:consume}),
|e1| and |e2| are each consumed exactly once; and hence |(,)| is linear it its
arguments.

\begin{wrapfigure}[5]{r}[0pt]{5cm} % lines, placement, overhang, width
\vspace{-6mm}
\begin{code}
f1 :: (Int,Int) -> (Int,Int)
f1 x = case x of (a,b) -> (a+a,0)

f2 :: (Int,Int) ⊸ (Int,Int)
f2 x = case x of (a,b) -> (b,a)
\end{code}
\end{wrapfigure}
So much for construction; what about pattern matching?  Consider
|f1| and |f2| defined here;
%
|f1| is an ordinary Haskell function. Even though the data constructor |(,)| has
a linear type, that does \emph{not} imply that the pattern-bound variables |a| and |b|
must be consumed exactly once; and indeed they are not.
And, thus |f1| does not have the linear type |(Int,Int) ⊸ (Int,Int)|.
Why not?  If the result of |(f1 t)| is consumed once, is |t| guaranteed to be consumed
once?  No: |t| is guaranteed to be evaluated once, but its first component is then
consumed twice and its second component not at all, contradicting \Fref{def:consume}.
%
In contrast, |f2| \emph{does} have a linear type: if |(f2 t)| is consumed exactly once,
then indeed |t| is consumed exactly once.
%
The key point here is that \emph{the same pair constructor works in both functions;
we do not need a special non-linear pair}.

% \begin{wrapfigure}[8]{r}[0pt]{3.5cm} \vspace{-6mm}
\begin{wrapfigure}[8]{r}[0pt]{4.5cm} \vspace{-8mm} 
\begin{code}
data [a] where
  []   :: [a]
  (:)  :: a ⊸ [a] ⊸ [a]
\end{code}
\begin{code}
(++) :: [a] ⊸ [a] ⊸ [a]
[]      ++ ys = ys
(x:xs)  ++ ys = x : (xs ++ ys)
\end{code}
\end{wrapfigure}
%  
The same idea applies to all existing Haskell data types: we (re-)define
their constuctors to use a linear arrow.  For example here is a declaration
of \HaskeLL{}'s list type:


%% \begin{wrapfigure}[4]{r}[0pt]{4cm} \vspace{-6mm} % lines, placement, overhang, width
%% \begin{code}
%% (++) :: [a] ⊸ [a] ⊸ [a]
%% []      ++ ys = ys
%% (x:xs)  ++ ys = x : (xs ++ ys)
%% \end{code}
%% \end{wrapfigure}
%
Just as with pairs, this is not a new, linear list type: this \emph{is}
\HaskeLL{}'s list type, and all existing Haskell functions will work
over it perfectly well.
Even better, many list-based functions are in fact linear, and
can be given a more precise type. For example we can write |(++)| as
follows:


This type says that if |(xs ++ ys)| is consumed exactly once, then
|xs| is consumed exactly once, and so is |ys|, and indeed our type
system will accept this definition.

As before, giving a more precise type to |(++)| only {\em strengthens} the
contract that |(++)| offers to its callers; \emph{it does not restrict
  its usage}. For example:
\begin{code}
  sum :: [Int] ⊸ Int
  f :: [Int] ⊸ [Int] -> Int
  f xs ys = sum (xs ++ ys) + sum ys
\end{code}
Here the two arguments to |(++)| have different multiplicities, but
the function |f| guarantees that it will consume |xs| exactly once if
|(f xs ys)| is consumed exactly once.

For an existing language, being able to strengthen |(++)|, and similar
functions, in a {\em backwards-compatible} way is a huge boon.  Of
course, not all functions are linear: a function may legitimately
demand unrestricted input.  For example, the function |f| above
consumes |ys| twice, and so
|f| needs an unrestricted arrow for that argument.
\label{sec:compatibility}

% The type of |(++)| tells us that if we have a list |xs| with
% multiplicity $1$, appending any other list to it will never duplicate
% any of the elements in |xs|, nor drop any element in
% |xs|\footnote{This follows from parametricity.  In order to {\em free}
%   linear list elements, we must pattern match on them to consume them,
%   and thus must know their type (or have a type class instance).
%  Likewise to copy them.}.

Finally, we can use the very same pairs and lists
types to contain linear values (such as mutable arrays) without
compromising safety.  For example:
\begin{code}
upd :: (MArray Char, MArray Char) ⊸ Int -> (MArray Char, MArray Char)
upd (a1, a2) n  | n >= 10    = (write a1 n 'x', a2)
                | otherwise  = (write a2 n 'o', a1)
\end{code}

\subsection{Unrestricted data constructors}
\label{sec:non-linear-constructors}

Suppose I want to pass a linear |MArray| and an unrestricted |Int| to a function |f|.
We could give |f| the signature |f :: MArray Int ⊸ Int -> MArray Int|.  But suppose
we wanted to uncurry the function; we could then give it the type
\begin{code}
  f :: (MArray Int, Int) ⊸  MArray Int
\end{code}
But this is no good: now |f| is only allowed to use the |Int| linearly, but it
might actually use it many times.  For this reason it is extremely useful to be
able to declare data constructors with non-linear types, like this:
\begin{code}
  data PLU a b where { PLU :: a ⊸ b -> PLU a b }

  f :: PLU (MArray Int) Int ⊸  MArray Int
\end{code}
Here we use \textsc{gadt}-style syntax to give an explicit type signature to the data
constructor |PLU|, with mixed linearity. \improvement{Explain here that
non-gadt syntax is linear}
Now, when \emph{constructing} a |PLU| pair the type of the constructor means
that we must always supply an unrestricted second argument; and dually
when \emph{pattern-matchinng} on |PLU| we are therefore free use the second argument
in an unrestricted way, even if the |PLU| value itself is linear.

Instead of defining a pair with mixed linearity, we can also write
\begin{code}
  data Unrestricted a where { Unrestricted :: a → Unrestricted a }

  f :: (MArray Int, Unrestricted Int) ⊸  MArray Int
\end{code}
The type |(Unrestricted t)| is very like ``|!t|'' in linear logic, but to us
it is just a library data type.
We saw it used in \fref{fig:linear-array-sigs}, where the result of |read| was
a pair of a linear |MArray| and an unrestricted array element:
\begin{code}
  read :: MArray a ⊸ Int -> (MArray a, Unrestricted a)
\end{code}
Note that, according to the definition in \fref{sec:consumed},
if a value of type |(Unrestricted t)| is consumed exactly once,
that tells us nothing about how the argument of the data constructor is consumed:
it may be consumed many times or not at all.

\subsection{Multiplicity polymorphism}
\label{sec:lin-poly}
A linear function provides more guarantees to its caller than
a non-linear one~---~it is more general.  But the higher-order
case thickens the plot. Consider the standard |map| function over
(linear) lists:
\begin{code}
map f []      = []
map f (x:xs)  = f x : map f xs
\end{code}
It can be given the two following incomparable types:
  |(a ⊸ b) -> [a] ⊸ [b]|  and
  |(a -> b) -> [a] -> [b]|.
%
  Thus, \HaskeLL{} features quantification over multiplicities and
  parameterised arrows (|A → _ q B|).  Using these, |map| can be given
  the following most general type: |∀p. (a -> _ p b) -> [a] -> _ p
  [b]|.
%
Likewise, function composition and |foldl| (\textit{cf.} \Fref{sec:freezing-arrays})
can be given the following general types:
\begin{code}
foldl :: forall p q. (a → _ p b → _ q  a) -> a → _ p [b] → _ q a

(∘) :: forall p q. (b → _ p c) ⊸ (a → _ q b) → _ p a → _ (p · q) c
(f ∘ g) x = f (g x)
\end{code}
The type of |(∘)| says that two functions that accept arguments of arbitrary
multiplicities (|p| and |q| respectively) can be composed to form a
function accepting arguments of multiplicity |p·q| (\ie the
product of |p| and |q| --- see \fref{def:equiv-multiplicity}).
%
Finally, from a backwards-compatibility perspective, all of these
subscripts and binders for multiplicity polymorphism can be
ignored. Indeed, in a context where client code does not use
linearity, all inputs will have unlimited multiplicity, $ω$, and transitively all
expressions can be promoted to $ω$. Thus in such a context the
compiler, or indeed documentation tools, can even altogether hide
linearity annotations from the programmer when this language
extension is not turned on.

\subsection{Linear input/output} \label{sec:linear-io}

In \fref{sec:io-protocols} we introduced the |IOL|
monad.\footnote{|IOL p| is not a monad in the strict sense, |p| and
  |q| can be different in |bindIOL|, it is however a relative
  monad~\cite{altenkirch_monads_2010}. The details, involving the
  functor |data Mult p a = Mult :: a -> _ p Mult p a| and linear
  arrows, are left as an exercise to the reader}
But how does it work?  |IOL|
is just a generalisation of the |IO| monad, thus:
\begin{code}
  type IOL p a
  returnIOL :: a -> _ p IOL p a
  bindIOL   :: IO p a ⊸ (a -> _ p IOL q b) ⊸ IOL q b
\end{code}
The idea is that if |m :: IOL 1 t|, then |m| is an input/output
computation that returns a linear value of type |t|.  But what does it mean to
``return a linear value'' in a world where linearity applies only to
function arrows?  Fortunately, in the world of monads each computation
has an explicit continuation, so we just need to control the linearity of
the continuation arrow.  More precisely, in an application |m `bindIOL` k|
where |m :: IOL 1 t|, we need the continuation |k| to be linear, |k :: t ⊸ IOL q t'|.
And that is captured by the multiplicity-polymorphic type of |bindIOL|.

Even though they have a different type than usual, the bind and return
combinators of |IOL| can be used in the familiar way. The difference
with the usual monad is that multiplicities may be mixed, but this
poses no problem in practice.  Consider
\begin{code}
  do  { f <- openFile s   -- |openFile :: FilePath -> IOL 1 (File ByteString)|
      ; d <- getDate      -- |getDate  :: IOL ω Date|
      ; e[f,d] }
\end{code}
Here |openFile| returns a linear |File| that should be closed, but |getDate| returns
an ordinary non-linear |Date|.  So this sequence of operations has mixed linearity.
Nevertheless, we can combine them with |bindIOL| in the usual way:
\begin{code}
  openFile s `bindIOL` \f ->
  getData    `bindIOL` \d ->
  e[f,d]
\end{code}
Such an interpretation of the |do|-notation requires Haskell's
\texttt{-XRebindableSyntax} extension, but if linear I/O becomes
commonplace it would be worth considering a more robust solution.

Internally, hidden from clients, \textsc{ghc} actually implements |IO| as a function,
and that implementation too is illuminated by linearity, like so:
\begin{code}
data World
newtype IOL p a = IOL (unIOL :: World ⊸ IORes p a)
data IORes p a where
  IOR :: World ⊸ a -> _ p IOR p a

bindIOL   :: IOL p a ⊸ (a -> _ p IOL q b) ⊸ IOL q b
bindIOL (IOL m) k = IOL (\w ->   case m w of
                                   IOR w' r -> unIOL (k r) w')
\end{code}
A value of type |World| represents the state of the world, and is
threaded linearly through I/O computations.  The linearity of the
result of the computation is captured by the |p| parameter of |IOL|,
which is inherited by the specialised form of pair, |IORes| that an
|IOL| computation returns.  All linearity checks are verified by the
compiler, further reducing the size of the trusted code base.
\subsection{Linearity and strictness}

It is tempting to suppose that, since a linear function consumes its
argument exactly once, then it must also be strict.  But not so!
For example
\begin{code}
f :: a ⊸ (a, Bool)
f x = (x, True)
\end{code}
Here |f| is certainly linear according to \fref{sec:consumed}, and
given the type of |(,)| in \fref{sec:linear-constructors}. That is, if |(f x)|
is consumed exactly once, then each component of its result pair is
consumed exactly once, and hence |x| is consumed exactly once.
But |f| is certainly not strict: |f undefined| is not |undefined|.


\section{\calc{}: a core calculus for \HaskeLL}
\label{sec:statics}
\label{sec:calculus}

It would be impractical to formalise all of \HaskeLL{}, so instead we
formalise a core calculus, \calc{}, which exhibits all the key features
of \HaskeLL{}, including data types and multiplicity polymorphism.  In this
way we make precise much of the informal discussion above.


\subsection{Syntax}
\newcommand{\pip}{\kern 1.18em || }
\label{sec:syntax}

\begin{figure}
  \begin{minipage}{0.4 \textwidth} \centering  
  \figuresection{Multiplicities}
  \begin{align*}
    π,μ &::= 1 ~||~ ω ~||~ p ~||~ π+μ ~||~ π·μ
  \end{align*}
  \end{minipage}%
  \begin{minipage}{0.4 \textwidth} \centering
  \figuresection{Contexts}
  \begin{align*}
    Γ,Δ & ::=  (x :_{μ} A), Γ \quad||\quad –
  \end{align*}
  \end{minipage}

  \figuresection{Datatype declaration}
  \begin{align*}
    \data D~p_1~…~p_n~\mathsf{where} \left(c_k : A₁ →_{π₁} ⋯    A_{n_k} →_{π_{n_k}} D\right)^m_{k=1}
  \end{align*}

  \figuresection{Types}
  \begin{align*}
  A,B ::= A →_π B \quad || \quad  ∀p. A \quad || \quad D~p_1~…~p_n
  \end{align*}

  \figuresection{Terms}
  \begin{align*}
    e,s,t,u & ::= x & \text{variable} \\
            & \pip λ_π (x{:}A). t & \text{abstraction} \\
            & \pip t s & \text{application} \\
            & \pip λp. t & \text{multiplicity abstraction} \\
            & \pip t π & \text{multiplicity application} \\
            & \pip c t₁ … t_n & \text{data construction} \\
            & \pip \case[π] t {c_k  x₁ … x_{n_k} → u_k}  & \text{case} \\
            & \pip \flet[π] x_1 : A₁ = t₁ … x_n : A_n = t_n \fin u & \text{let}
  \end{align*}

  \caption{Syntax of \calc{}}
  \label{fig:syntax}
  \label{fig:contexts}
\end{figure}

The term syntax of \calc{} is that of a type-annotated (\textit{à la}
Church) simply-typed $λ$-calculus with let-definitions
(\fref{fig:syntax}).  It includes multiplicity polymorphism, but to avoid clutter
we omit ordinary type polymorphism.

\calc{} is an explicitly-typed language: each binder is annotated with
its type and multiplicity; and multiplicity abstraction and application
are explicit.  \HaskeLL{} will use type inference to fill in
much of this information, but we do not address the challenges of type
inference here.

The types of \calc{} (see \fref{fig:syntax}) are simple types with
arrows (albeit multiplicity-annotated ones), data types, and
multiplicity polymorphism.
We use the following abbreviations:
\(A → B ≝  A →_ω B\) and
\(A ⊸ B ≝ A →_1 B\).

Data type declarations (see \fref{fig:syntax}) are of the following form:
\begin{align*}
  \data D~p_1~…~p_n~\mathsf{where} \left(c_k : A₁ →_{π₁} ⋯    A_{n_k} →_{π_{n_k}} D\right)^m_{k=1}
\end{align*}
The above declaration means that \(D\) is parameterized over \(n\) multiplicities $p_i$ and has \(m\) constructors \(c_k\),
each with \(n_k\) arguments. Arguments of
constructors have a multiplicity, just like arguments of functions: an
argument of multiplicity $ω$ means that consuming the data constructor once
makes no claim on how often that argument is consumed (\fref{def:consume}).
All the variables in the multiplicities $π_i$ must be among
$p_1…p_n$; we write $π[π_1…π_n]$ for the substitution of $p_i$ by
$π_i$ in $π$.

% -------------------------------------------------
\subsection{Static semantics}
\label{sec:typing-contexts}

%%% typing rule macros %%%
\newcommand{\apprule}{\inferrule{Γ ⊢ t :  A →_π B  \\   Δ ⊢ u : A}{Γ+πΔ ⊢ t u  :  B}\text{app}}
\newcommand{\varrule}{\inferrule{ }{ωΓ + x :_1 A ⊢ x : A}\text{var}}
\newcommand{\caserule}{\inferrule{Γ   ⊢  t  : D~π_1~…~π_n \\ Δ, x₁:_{πμ_i[π_1…π_n]} A_i, …,
      x_{n_k}:_{πμ_{n_k}[π_1…π_n]} A_{n_k} ⊢ u_k : C \\
      \text{for each $c_k : A_1 →_{μ_1} … →_{μ_{n_k-1}} A_{n_k} →_{μ_{n_k}} D~p_1~…~p_n$}}
    {πΓ+Δ ⊢ \case[π] t {c_k  x₁ … x_{n_k} → u_k} : C}\text{case}}
%%% /macros %%%

\begin{figure}
  \begin{mathpar}
    \varrule

    \inferrule{Γ, x :_{π} A  ⊢   t : B}
    {Γ ⊢ λ_π (x{:}A). t  :  A  →_q  B}\text{abs}

    \apprule

    \inferrule{Δ_i ⊢ t_i : A_i \\ \text {$c_k : A_1 →_{μ_1} … →_{μ_{n-1}}
        A_n →_{μ_n} D~p_1~…~p_n$ constructor}}
    {ωΓ+\sum_i μ_i[π₁…π_n]Δ_i ⊢ c_k  t₁ … t_n : D~π₁~…~π_n}\text{con}

    \caserule

    \inferrule{Γ_i   ⊢  t_i  : A_i  \\ Δ, x₁:_{π} A₁ …  x_n:_{π} A_n ⊢ u : C }
    { Δ+q\sum_i Γ_i ⊢ \flet[π] x_1 : A_1 = t₁  …  x_n : A_n = t_n  \fin u : C}\text{let}

    \inferrule{Γ ⊢  t : A \\ \text {$p$ fresh for $Γ$}}
    {Γ ⊢ λp. t : ∀p. A}\text{m.abs}

    \inferrule{Γ ⊢ t :  ∀p. A}
    {Γ ⊢ t π  :  A[π/p]}\text{m.app}
  \end{mathpar}

  \caption{Typing rules}
  \label{fig:typing}
\end{figure}

The static semantics of \calc{} is given in \fref{fig:typing}.  Each
binding in $Γ$, of form \(x :_π A\), includes a multiplicity $π$
(\fref{fig:syntax}).  The familiar judgement \(Γ ⊢ t : A\) should
be read as follows
\begin{quote}
 \(Γ ⊢ t : A\) asserts that consuming the term $t : A$ exactly once will
  consume each binding $(x :_{π} A)$ in $Γ$ with its multiplicity $π$.
\end{quote}
One may want to think of the \emph{types} in $Γ$ as
inputs of the judgement, and the \emph{multiplicities} as outputs.

The rule (abs) for lambda abstraction adds $(x :_{π} A)$ to the
environment $Γ$ before checking the body |t| of the abstraction.
Notice that in \calc{}, the lambda abstraction  $λ_π(x{:}A). t$
is explicitly annotated with multiplicity $π$.  Remember, this
is an explicitly-typed intermediate language; in \HaskeLL{}
this multiplicity is inferred.

The dual application rule (app) is more interesting:
$$\apprule$$
To consume |(t u)| once, we consume |t| once, yielding the
multiplicities in $Γ$, and |u| once, yielding the multiplicies in
$\Delta$.  But if the multiplicity $π$ on |u|'s function arrow is $ω$,
then the function consumes its argument not once but $ω$ times, so all
|u|'s free variables must also be used with multiplicity $ω$. We
express this by taking the {\em product} of the multiplicities in $\Delta$ and $π$,
thus $π\Delta$.  Finally we need to add together all the
multiplicities in $Γ$ and $π\Delta$; hence the context $Γ+πΔ$ in the
conclusion of the rule.

In writing this rule we needed to ``scale'' a context by
a multiplicity, and ``add'' two contexts.  We pause to define these operations.
\begin{definition}[Context addition]~
  \begin{align*}
    (x :_π A,Γ) + (x :_{μ} A,Δ) &= x :_{π+μ} A, (Γ+Δ)\\
    (x :_π A,Γ) + Δ &= x :_π A, Γ+Δ & (x ∉ Δ)\\
    () + Δ &= Δ
  \end{align*}
\end{definition}
\noindent
Context addition is total: if a variable occurs in both operands the
first rule applies (with possible re-ordering of bindings in $Δ$), if
not the second or third rule applies.

\begin{definition}[Context scaling]
  \begin{displaymath}
    π(x :_{μ} A, Γ) =  x :_{πμ} A, πΓ
  \end{displaymath}
\end{definition}

\begin{lemma}[Contexts form a module]
  The following laws hold:
  \begin{align*}
    Γ + Δ &= Δ + Γ &
    π (Γ+Δ) &= π Γ + π Δ\\
    (π+μ) Γ &= π Γ+ μ Γ \\
    (πμ) Γ &= π (μ Γ) &
    1 Γ &= Γ
  \end{align*}
\end{lemma}

These operations depend, in turn, on addition and multiplication of multiplicities.
The syntax of multiplicities is given in \fref{fig:syntax}.
We need the concrete multiplicities $1$ and $ω$ and, to support polymorphism,
multiplicity variables (ranged over by the metasyntactic
variables \(p\) and \(q\)) as well as formal sums and products of multiplicities.
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
module structure on typing contexts.

Returning to the typing rules in \fref{fig:typing}, the rule (let) is like
a combination of (abs) and (app).  Again, each $\flet$ binding is
explicitly annotated with its multiplicity.
%
The variable rule (var) uses a standard idiom:
\vspace{-3mm}
$$\varrule$$
This rule allows us to ignore variables with
multiplicity $ω$ (usually called weakening),
so that, for example $x :_1 A, y :_ω B ⊢ x : A$ holds
\footnote{Pushing weakening to the variable rule is
  classic in many $λ$-calculi, and in the case of linear logic,
  dates back at least to Andreoli's work on
  focusing~\cite{andreoli_logic_1992}.}. Note that the judgement
$x :_ω A ⊢ x : A$ is an instance of the variable rule, because
$(x :_ω A)+(x :_1 A) = x:_ω A$.

Finally, abstraction and application for multiplicity polymorphism
are handled straightforwardly by (m.abs) and (m.app).

\subsection{Data constructors and case expressions}
\label{sec:typing-rules}

The handling of data constructors and case expressions is a
distinctive aspect of our design.  For constructor applications, the rule
(con), everything is straightforward: we treat the data constructor in
precisely the same way as an application of a function with that data constructor's type.
This includes weakening via the $ωΓ$ context in the conclusion.
The (case) rule is more interesting:
$$\caserule$$
First, notice that the $\mathsf{case}$ keyword is annotated with a
multiplicity $π$; this is analogous to the explicit
multiplicity on a $\mathsf{let}$ binding.  It says how often the scrutinee (or,
for a $\mathsf{let}$, the right hand side) will be consumed.  Just as
for $\mathsf{let}$, we expect $π$ to be inferred from an un-annotated $\mathsf{case}$ in
\HaskeLL{}.

The scrutinee $t$ is consumed $π$ times, which accounts for the $πΓ$ in
the conclusion.  Now consider the bindings $(x_i :_{πμ_i[π_1…π_n]} A_i)$ in the
environment for typechecking $u_k$.  That binding will be linear only if
\emph{both} $π$ \emph{and} $π_i$ are linear; that is, only if we specify
that the scrutinee is consumed once, and the $i$'th field of the data constructor $c_k$
specifies that is it consumed once if the constructor is (\fref{def:consume}).
%
To put it another way, suppose one of the linear
fields\footnote{
Recall \fref{sec:non-linear-constructors}, which described
how each constructor can have a mixture of linear and non-linear fields.}
of $c_k$ is used non-linearly in $u_k$.  Then, $μ_i=1$ (it is a linear field),
so $π$ must be $ω$, so that $πμ_i=ω$.  In short, using a linear field non-linearly
forces the scrutinee to be used non-linearly, which is just what we want.
Here are some concrete examples:
\begin{center}\vspace{-3mm}  
\begin{code}
  fst  ::  (a,b) →  a     bigSpace    swap ::  (a,b) ⊸ (b,a)
  fst      (a,b)  =  a                swap     (a,b) =  (b,a)
\end{code}
\end{center}
Recall that both fields of a pair are linear (\fref{sec:linear-constructors}).
In |fst|, the second component of the pair is used non-linearly (by being
discarded) which forces the use of $\mathsf{case}_ω$, and hence a non-linear type
for |fst|.  But |swap| uses the components linearly, so we can use $\mathsf{case}_1$, giving
|swap| a linear type.

\subsection{Metatheory}
\label{sec:metatheory}

The details of the meta-theory of \calc{} are deferred to
\fref{appendix:dynamics}. Our goal is to establish two properties:
\begin{itemize}
\item That a pure linear interface can be implemented using mutations
  under the hood, like in \fref{sec:freezing-arrays}.
\item That the usage protocol resources is enforced by the type
  system, like in \fref{sec:io-protocols}
\end{itemize}

To that effect we introduce two semantics: a semantics with mutation
where typestates, such as whether an array is mutable or frozen, are
enforced dynamically and a pure semantics that tracks linearity
carefully, but where ``mutations'' are implemented as copying. Both
semantics are big step operational semantics with laziness in the
style of \citet{launchbury_natural_1993}.

The semantics are instantiated with the arrays of
\fref{sec:freezing-arrays}. They can be easily extended to support,
for instance, a real-world token and file handles as in
\fref{sec:io-protocols}.

We then prove the two semantics to be bisimilar from which we can
deduce:
\begin{theorem}[Observational equivalence]\label{thm:obs-equiv}
  The semantics with in-place mutation is observationally equivalent to the pure semantics.
\end{theorem}
\begin{theorem}[Progress]\label{thm:progress}
  Evaluation does not block. In particular, typestates need not
  be checked dynamically.
\end{theorem}

These statements are formalised and proven in \fref{appendix:dynamics}.

\subsection{Design choices \& trade-offs}
Let us review the design space allowed by \calc{}, the points in the space that
we chose, and the generalisations that we have left open.

\paragraph{Case rule}
It is possible to do without $\varid{case}_ω$, and have only $\varid{case}_1$.
Consider |fst| again.  We could instead have
\begin{code}
data Pair p q a b where
  Pair :: a → _ p b → _ q Pair p q a b

fst :: Pair 1 ω a b ⊸ a
fst x = case _ 1 x of Pair a b -> a
\end{code}
But now multiplicity polymorphism infects all basic data types (such as pairs), and it
is hard to forsee all the consequences.  Moreover, |let| is annotated so it seems
reasonable to annotate |case| in the same way.

To put it another way, $\varid{case}_ω$ allows us to meaningfully inhabit
|forall a b. Unrestricted (a,b) ⊸ (Unrestricted a, Unrestricted b)|, while linear logic
does not.

\paragraph{Subtyping}
Because the type $A⊸B$ only strengthens the contract of its elements
compared to $A→B$, one might expect the type $A⊸B$ to be a subtype of $A→B$.
But while \calc{} has \emph{polymorphism}, it does not have \emph{subtyping}.
For example, if
\begin{code}
  f :: Int ⊸ Int
  g :: (Int -> Int) -> Bool
\end{code}
then the call |(g f)| is ill-typed, even though |f| provides more
guarantees than |g| requires.
However, |g| might well be multiplicity-polymorphic, with type
|forall p. (Int -> _ p Int) -> Bool|; in which case |(g f)| is, indeed, typeable.
Alternatively, $η$-expansion to |g (\x. f x)|
makes the expression typeable, as the reader may check.

The lack of subtyping is a deliberate choice in our design: it is well
known that Hindley-Milner-style type inference does not mesh well with
subtyping (see, for example, the extensive exposition by
\citet{pottier_subtyping_1998}).
%
\HaskeLL{} on the other hand has limited support for subtyping:
calls like |(g f)| are well typed, and are elaborated to
$η$-expansions in \calc{}.

\paragraph{Polymorphism} Consider the definition: ``|id x = x|''.
%% \begin{code}
%% id x = x  
%% \end{code}
Our typing rules would validate both |id :: Int → Int| and |id :: Int ⊸ Int|.
So, since we think of multiplicities ranging over $\{1,ω\}$, surely we should
also have |id :: forall p. Int → _ p Int|?  But as it stands, our rules do
not accept it. To do so we would need $x :_p Int ⊢ x : Int$.  Looking
at the (var) rule in \fref{fig:typing}, we can prove that premise by case analysis,
trying $p=1$ and $p=ω$.
But if we had a richer domain of multiplicities, including
$0$ (see \fref{sec:extending-multiplicities}), we would be able to prove $x :_p Int ⊢ x : Int$, and rightly
so because it is not the case that |id :: Int → _ 0 Int|.

For now, we accept more conservative rules, in order to hold open the possiblity
of extending the multiplicity domain later.  But there is an up-front cost,
of somewhat less polymorphism than we might expect.  We hope that experience will
lead us to a better assessment of the costs/benefit trade-off here.

\section{Implementing \HaskeLL}
\label{sec:implementation}
\label{sec:impl}

We implement \HaskeLL{} on top of the leading Haskell compiler,
\textsc{ghc}, version 8.2\footnote{github URL suppressed for anonymous review}.
We modify type inference and
type-checking in the compiler. Neither the intermediate language~\cite{sulzmann_fc_2007}
nor the run-time system are affected.
%
Our implementation of multiplicity polymorphism is incomplete, but the current
prototype is sufficient for the examples and case studies presented in
in this paper.
%
Our \HaskeLL{} implementation is compatible with most, but not all, of
\textsc{ghc}'s extensions (one notable incompatible extension is
pattern-synonyms, the details of which have yet to be worked out).

In order to implement the linear arrow, we followed the design of
\calc{} and added a multiplicity annotation to arrows, as an
additional argument of the type constructor for arrows of
\textsc{ghc}'s type checker. The constructor for arrow types is
constructed and destructed frequently in \textsc{ghc}'s type checker, and this
accounts for most of the modifications to existing code.

As suggested in \fref{sec:typing-contexts}, the multiplicities are an
output of the algorithm. In order to infer the multiplicities of
variables in the branches of a |case| expression we need a way to join
the output of the branch. We use a supremum operation on
multiplicities where $1∨0 = ω$ ($0$ stands for a variable absent
in a branch).

Implementing \HaskeLL{}
%% \manuel{which branch? link? JP: Linguistically ``this branch'' refers to the
%%   case branch of the previous parag.}
affects 1,152 lines of \textsc{ghc} (in subsystems of the compiler
that together amount to more than 100k lines of code), including 444 net extra lines. A new
file responsible for multiplicity operations as well as the files
responsible for the environment manipulation and type inference of
patterns account for almost half of the affected lines. The rest spans
over a 100 files, most of which have 2 or 3 lines modified to account
for the extra multiplicity argument of the arrow constructor.
%% This work required roughly 1 man-month to complete.

These figures vindicate our claim that \HaskeLL{} is easy to integrate into an
existing implementation: despite \textsc{ghc} being 25 years old, we 
implement a first version of \HaskeLL{} with reasonable effort.

% \section{Applications}
\section{Evaluation and Case Studies}
\label{sec:evaluation}
\label{sec:applications}

% In contrast with many proposed linear type systems,
While many linear type systems have been proposed,
%
a {\em retrofitted} linear type system for a mature language like Haskell offers
the opportunity to implement non-trivial applications mixing linear and
non-linear code, I/O, etc., and observe how linear code interacts with existing
libraries and the optimiser of a sophisticated compiler.

Our first method for evaluating the implementation is to simply compile a large
existing code base together with the following changes: (1) all data constructors are
linear by default, as implied by the new type system; and (2) we update standard
list functions to have linear types (|++|, |concat|, |uncons|).
%
Under these conditions, we verified that the base GHC libraries and the nofib
benchmark suites compile successfully: 195K lines of Haskell, providing
preliminary evidence of backwards compatibility.

In the remainder of section, we describe case-studies implementated with the modified
\ghc  of \fref{sec:implementation}.
%
In \fref{sec:industry}, we propose further applications for \HaskeLL, which we
have not yet implemented, but which motivate this work.


% \subsection{Serialised tree traversals}
\subsection{Application 1: Computing directly with serialised data}
%------------------------------------------------------------------
\label{sec:cursors}

While \fref{sec:freezing-arrays} covered simple mutable arrays, we now
turn to a related but more complicated application: operating directly on binary,
serialised representations of algebraic data-types
(as in \citet{vollmer_gibbon_2017}).
% and \cite{yang_compact_2015}.
%
%% Modern service-oriented software, running in data-centers, spends a great deal
%% of time (de)serialising data received over the network.  
%
The motivation is that programs are increasingly decoupled into separate (cloud)
services that communicate via serialised data in text or binary formats, carried
by remote procedure calls.
%
The standard approach is to deserialise data into an in-heap, pointer-based representation,
% (that is, a recursive Haskell data type),
process it, and then serialise the result for transmission.
%
This process is exceedingly inefficient, but tolerated, because the alternative
--- computing directly with serialised data --- is far too difficult to program.
%
Nevertheless, the potential performance gain of working directly with serialised
data has motivated small steps in this direction:
%
libraries like ``Cap'N Proto''~\footnote{{\url{https://capnproto.org/}}} enable unifying
in-memory and on-the-wire formats for simple product types (protobufs).

Here is an unusual case where {advanced types can yield {\em performance}} by
making it practical to code in a previously infeasible style: accessing
serialised data at a fine grain without copying it.

\begin{wrapfigure}[8]{r}[34pt]{8.5cm}
\vspace{-4mm}
\begin{code}
data Tree = Leaf Int | Branch Tree Tree
pack    :: Tree ⊸ Packed [Tree]
unpack  :: Packed [Tree] ⊸ Tree
caseTree ::  Packed (Tree:r) -> _ p
             (Packed (Int:r) -> _ p a) ⊸
             (Packed (Tree:Tree:r) -> _ p a) ⊸ a
\end{code}
%read :: Storable a => Packed (a:r) ⊸ (a, Packed r)
\end{wrapfigure}
%
The interface on the right gives an example of type-safe, {\em read-only}
access to serialised data for a particular datatype.
%
A |Packed| value is a pointer to raw bits (a bytestring), indexed by the
types of the values contained within.  We define a {\em type-safe} serialisation
layer as one which {\em reads} byte-ranges only at the type and size they were
originally {\em written}.  This is a small extension of the memory safety we
already expect of Haskell's heap --- extended to include the contents of
bytestrings containing serialised data\footnote{The additional safety ensured
  here is lower-stakes than typical memory-safety, as, even it is violated, the
  serialised values do not contain pointers and cannot segfault the program
  reading them.}.
%
To preserve this type safety, the |Packed| type {\em must} be abstract.
%
Consequently, a client of the module defining |Tree| need not be privy to the
memory layout of its serialisation.

If we cannot muck about with the bits inside a |Packed| directly, then we can
still retrieve data with |unpack|, \ie, the traditional, {\em copying},
approach to deserialisation.  Better still is to read the data {\em without}
copying.  We can manage this feat with |caseTree|, which is analogous to the
expression ``|case e of {Leaf ... ; Branch ...}|''.
%
Lacking built-in syntax, |(caseTree p k1 k2)| takes two continuations
corresponding to the two branches of the case expression.
%
Unlike the case expression, |caseTree| operates on the packed byte stream, reads
a tag byte, advances the pointer past it, and returns a type-safe pointer to the
fields (\eg |Packed [Int]| in the case of a leaf).
%% \begin{code}
%%   caseTree  (pack (Leaf 3))
%%             (\ p::Packed [Int] -> ...)
%% \end{code}

%% |caseFoo| abstracts over whether or not a {\em tag} value is included in the
%% serialisation, if not, it becomes a cast and a |Foo| requires only 16 bytes.

%% When handling datatypes with multiple constructors, their serialisations will
%% first include a {\em tag} byte indicating which variant; but |Foo| is a product
%% type, requiring only 16 bytes.

%% A serialised |Foo| fills exactly 17 bytes, and |caseFoo| returns a reference to
%% the 16-byte suffix containing the two fields.

It is precisely to access multiple, consecutive fields that |Packed| is indexed
by a {\em list} of types as its phantom type parameter.  Individual atomic
values (|Int|, |Double|, etc) can be read one at a time with a lower-level
|read| primitive, which can efficiently read out scalars and store them in
registers:
\begin{code}
  read :: Storable a => Packed (a:r) ⊸ (a, Packed r)  
\end{code}
%
%% \begin{code}
%%   f :: Packed [Foo] -> Double
%%   f p =  let  (n,p')   = read (caseFoo p);  (m,p'')  = read p' in fromIntegral n + m
%% \end{code}

\begin{wrapfigure}[8]{r}[0pt]{7.0cm} % lines, placement, overhang, width
\vspace{-6mm}
\begin{code}
sumLeaves :: Packed [Tree] -> Int
sumLeaves p = fst (go p)
  where go p =  caseTree p 
                  read -- Leaf case
                  (\p2 ->  let  (n,p3) = go p2
                                (m,p4) = go p3
                           in (n+m,p4))
\end{code}
\end{wrapfigure}
Putting it together, we can write a function that consumes serialised data, such
as |sumLeaves|, shown on the right.
%
Indeed, we can even use |caseTree| to implement |unpack|, turning it into safe
``client code'' -- sitting outside the module that defines |Tree| and the
trusted code establishing its memory representation.

In this read-only example, linearity was not essential, only phantom types.
Next we consider an \textsc{API} for writing |Packed
[Tree]| values bit by bit, where linearity is key.
%
In particular, can we also implement |pack| using a public interface?
%% \improvement{aspiwack: I don't think the type argument of |Packed| can
%%   quite be considered a typestate}

%% Indeed, linearity and {typestate} are both key to to a safe \textsc{api} for
%% manipulating serialised data.  But, as with arrays, linearity is only necessary
%% for writing.  A read-only interface on serialised data can work fine without it.

\subsubsection{Writing serialised data}
%------------------------------------------

%% The mutable arrays of \fref{sec:freezing-arrays} were homogenous --- with
%% evenly-spaced, aligned elements.  In contrast, binary-serialised data structures
%% contain primitive values of various widths, at unaligned byte-offsets.
%
%% A pointer into a buffer containing serialised output is similar to a constructor
%% method for a regular heap object.  It must ensure that all fields are initialised, at
%% the proper addresses and with values of the correct type.
%
To create a serialised data constructor, we must write a tag, followed by the
fields.
%
A {\em linear} write pointer can ensure all fields are initialised, in order.
We use a type ``|Needs|'' for write pointers, parameterised by (1) a
list of remaining things to be written, and (2) the type of the final value
which will be initialised once those writes are performed.  For example, after
we write the tag of a |Leaf| we are left with:
%\begin{code}
``|Needs [Int] Tree|'' ---
%\end{code}
an {\em obligation} to write the |Int| field, and a {\em promise} to receive
a |Tree| value at the end (albeit a packed one).
%
%% |Needs| is parameterised both by {\em obligations}, that an |Int| and then a
%% |Double| must be written, and by the resulting, immutable value that will be
%% available upon completing those writes (|Foo|).

To write an individal number, we provide a primitive that shaves one
element off the type-level list of obligations (a counterpart to |read|, above):
As with mutable arrays, this |write| operates in-place on the buffer, in spite
being a pure function.
%
\begin{code}
  write :: Storable a => a ⊸ Needs (a:r) t ⊸ Needs r t
\end{code}
%
When the list of outstanding writes is empty, we can retrive a readable packed buffer.
Just as when we froze arrays (\fref{sec:freezing-arrays}), the immutable value
is {\em unrestricted}, and can be used multiple times:
%
\begin{code}
  finish :: Needs [] t ⊸ Unrestricted (Packed [t])
\end{code}
%
Finalizing written values with |finish| works hand in hand with allocating new
buffers in which to write data (similar to |newMArray| from \fref{sec:freezing-arrays}):
%
\begin{code}
  newBuffer :: (Needs [a] a ⊸ Unrestricted b) ⊸ b
\end{code}
%
We also need to explicitly let go of linear input buffers we've exhausted.
\begin{code}
  done :: Packed [] ⊸ ()
\end{code}

The primitives |write|, |read|, |newBuffer|, |done|, and |finish| are {\em general}
operations for serialised data, whereas |caseTree| is datatype-specific.
Further, the module that defines |Tree| exports a datatype-specific way to 
{\em write} each serialised data constructor:
%
% startFoo :: Needs (Foo:r) t ⊸ Needs (Int:Double:r) t
\begin{code}
startLeaf    :: Needs (Tree : r) t ⊸ Needs (Int : r) t
startBranch  :: Needs (Tree : r) t ⊸ Needs (Tree : Tree : r) t
\end{code}
Operationally, |start*| functions write only the tag, hiding the exact
tag-encoding from the client, and leaving field-writes as future obligations.
%
With these building blocks, we can move |pack| and |unpack| outside of the
private code that defines |Tree|s, which has this minimal interface:
\begin{code}
module TreePrivate( Tree(..), caseTree, startLeaf, startBranch)
module DataPacked( Packed, Needs, read, write, newBuffer, finish, done )
\end{code}
%
%% After writing the two fields to |p| in this example, we need a way to finalize
%% the operation and convert the write pointer to a read pointer:
%
%% Just as when we converted mutable arrays to immutable arrays, here the immutable
%% |Foo| can be read multiple times.
%
%% It is not, however, a {\em normal} heap representation of |Foo|,
%% but rather an isomorphic, serialised representation: |Packed [Foo]|.  Nevertheless,
%% everything in a |Foo| can be read in a type-safe way directly from the
%% serialised buffer.
%
%% These operations themselves go into the trusted codebase.  Internally, we choose
%% a one-byte representation for the |Leaf|/|Branch| tags, and write these to the
%% output stream, immediately before the left-to-right serialised fields.  Yet
%% ``|write leafTag|'' would not suffice, as its type differs from |startLeaf| above.
%% % it would be |Needs (Tag:r) t ⊸ Needs r t`
%% A coercion is needed internally to reify the knowledge
%% that ``a tag plus an integer equals a leaf record, and thus a tree''.
%
On top of the safe interface, we can of course define higher-level construction
routines, such as for writing a complete |Leaf|:
%
%   writeLeaf n p = write n (startLeaf p)
\begin{code}
  writeLeaf n = write n ∘ startLeaf 
\end{code}
%
Now we can allocate and initialize a complete tree --- equivalent to |Branch
(Leaf 3) (Leaf 4)|, but without ever creating the non-serialised values --- as
follows:
\begin{code}
newBuffer (finish ∘ writeLeaf 4 ∘ writeLeaf 3 ∘ startBranch) :: Packed [Tree]
\end{code}

Finally, we have what we need to build a map function that logically operates
on the leaves of a tree, but reads serialised input and writes serialised
output.
%
Indeed, in our current \HaskeLL{} implementation ``|mapLeaves (+1) tree|'' touches {\em
  only} packed buffers --- it performs zero Haskell heap allocation!
%
We will return to this map example and benchmark it in \fref{sec:cursor-benchmark}.
%
With the safe interface to serialised data, functions like |sumLeaves| and
|mapLeaves| are not burdensome to program.  The code for |mapLeaves| is shown
below.

%\begin{wrapfigure}[12]{r}[0pt]{7.0cm} % lines, placement, overhang, width
%\vspace{-6mm}
\begin{code}
module TreePublic (pack, unpack, writeLeaf, sumLeaves, mapLeaves)
...
mapLeaves :: (Int->Int) -> Packed Tree ⊸ Packed Tree
mapLeaves fn pt = newBuffer (extract ∘ go pt)
  where
    extract (inp,outp) = case done inp of () -> finish outp
    go :: Packed (Tree:r) ⊸ Needs (Tree:r) t ⊸ (Packed r, Needs r t)
    go p = caseTree p  (\p o ->  let (x, p') = read p  in ( p', writeLeaf (fn x) o))
                       (\p o ->  let (p',o') = go p (writeBranch o) in go p' o')
\end{code}
%\end{wrapfigure}
%The inner loop linearly updates a pair of a read- and write-pointer.

%% \improvement{This section should assert that the abstraction is
%%   practical to program with, even comfortable.}


% \subsubsection{Linear vs. non-linear and compiler optimisations}
\subsubsection{A version without linear types}\label{sec:st-cursors}

How would we build the same thing in Haskell without linear types?  It may appear
that the ST monad is a suitable choice:

\begin{code}
writeST :: Storable a => a -> Needs' s (a:r) t -> ST s (Needs' s r t)  
\end{code}
Here we use the same typestate associated with a |Needs| pointer, while also
associating its mutable state with the |ST| session indexed by |s|.
%
% As in \fref{sec:freezing-arrays}, we rely on using an unsafe
% ... must extend the trusted code base.
Unfortunately, not only do we have the same trouble with freezing in the absence
of linearity (|unsafeFreeze|, \fref{sec:freezing-arrays}), we also
have an {\em additional} problem not present with arrays:
%
namely, a non-linear use of a |Needs| pointer can ruin our type-safe
deserialisation guarantee!
%
For example, we can write a |Leaf| and a |Branch| to the same pointer in an
interleaved fashion.  Both will place a tag at byte 0; but the leaf will place
an integer in bytes 1-9, while the branch will place another tag at byte 1.
%
%% \Red{If we define a type-safe serialisation interface as one where every read at a
%% type returns a whole value written at the same type, then this is a violation.}
We can receive a corrupted 8-byte integer, clobbered by a tag from an
interleaved ``alternate future''.

% Rehabilitating an ST-based formulation
Fixing this problem would require switching to an indexed monad with additional
type-indices that model the typestate of all accessible pointers, which would in
turn need to have static, type-level identifiers.  That is, it would require
{\em encoding} linearity after all, but in a way which would become very
cumbersome as soon as several buffers are involved.

\subsubsection{Benchmarking compiler optimisations}
\label{sec:cursor-benchmark}

\begin{figure}
  \hspace{-2mm}%
  \begin{minipage}{1.04 \textwidth}
  \hspace{-2mm}%
  \includegraphics[width=0.5 \textwidth]{figures/sumtree_all_plot_baseline_unpack-repack.pdf}
  \includegraphics[width=0.5 \textwidth]{figures/maptree_plot_baseline_unpack-repack.pdf}    
  \end{minipage}
\caption{Speedup of operating directly on serialised data, either using
  linear-types or the ST monad, as compared to fully unpacking, processing,
  and repacking the data.  For reference, a ``pointer-based'' version is also
  included, which doesn't operate on serialised data at all, but instead normal
  heap objects --- it represents the hypothetical performance of ``unpack-repack''
  if (de)serialisation were instantaneous.}
\label{fig:pack-bench}
\end{figure}

Finally, as shown in \fref{fig:pack-bench}, there are some unexpected
performance consequences from using a linear versus a monadic, ST style in
\ghc.
%
Achieving allocation-free loops in \ghc{} is always a challenge --- 
tuple types and numeric types are lazy and ``boxed'' as heap objects by default.
%
As we saw in the |sumLeaves| and |mapLeaves| examples, each recursive call returned a tuple
of a result and a new pointer.  In a monadic formulation, an expression of type
|m a|, for |Monad m|, implies that the ``result'' type |a|, of kind |*|, must be a
{\em lifted} type.  Nevertheless, in some situations, for some monads, the
optimiser is able to deforest data constructors returned by monadic actions.
%
In the particular case of |fold| and |map| operations over serialised trees,
unfortunately, we are currently unable to eliminate all allocation from
|ST|-based implementations of the algorithms.

For the linearly-typed code, however, we have more options.  \ghc{} has the ability to
directly express unboxed values such as a tuple |(# Int#, Double# #)|, which
fills two registers and inhabits an unboxed kind distinct from |*|.
%
In fact, the type of a combinator like |caseTree| is a good fit for the recent
``levity polymorphism'' addition to
\ghc{}~\cite{eisenberg_levity_2017}.  
Thus we permit the branches of the |case| to return unlifted, unboxed types, and
give |caseTree| a more general type:

\begin{code}
caseTree :: forall (rep :: RuntimeRep) (res :: TYPE rep) b.
  Packed (Tree:b) -> (Packed (Int:b) ⊸ res) -> (Packed (Tree:Tree:b) ⊸ res) -> res
\end{code}

This works because we do not need to {\em call} a function with |res| as
argument (and thus unknown calling conventions) only return it.
%
Using this approach, we were able to ensure by construction that the
``linear/packed'' implementations in \fref{fig:pack-bench} were completely
non-allocating, rather than depending on the optimiser.
%
This results in better performance for the linear, compared to monadic version
of the serialised-data transformations.

The basic premise of \fref{fig:pack-bench} is that a machine in the network
receives, processes, and transmits serialized data (trees).
%
We consider two simple benchmarks: |sumLeaves| and |mapTree (+1)|.
%% , a |fold| and a |map| respectively: (1) summing the
%% leaves of a tree, and (2) adding one to the leaves of a tree, producing a new
%% tree.
%
The baseline is the traditional approach: deserialise, transform, and reserialise,
the ``unpack-repack'' line in the plots.  Compared to this baseline,
{\em processing the data directly in its serialised form results in speedups of over
20$\times$ on large trees}.
%
What linear types makes safe, is also efficient.

The experiment was conducted on a Xeon E5-2699 CPU (2.30GHz, 64GB memory) using
our modified version of \ghc{} 8.2 (\fref{sec:impl}).  Each
data point was measured by performing many trials and taking a linear regression
of iteration count against time\footnote{using the criterion library~\cite{osullivan_criterion_2013}}.
%
This process allows for accurate measurements of both small and large times.  The
baseline unpack-repack tree-summing times vary from 25ns to 1.9 seconds at
depths 1 and 24 respectively.  Likewise, the baseline mapping times vary from
215ns to 2.93 seconds.
%
We use a simple contiguous implementation of buffers for
serialisation\footnote{A full, practical implementation should include growable
  or doubling buffers.}.
%
At depth 20, one copy of the tree takes around 10MB, and towards the right half
of the plot we see tree size exceeding cache size.


% -------------------------------
{\if{0}
    Let us look back to the array-freezing \textsc{api} of
    \fref{sec:freezing-arrays}. And push the boundaries to a new range of
    applications inspired by \citet{vollmer_gibbon_2017}.

    \improvement{aspiwack: I've spent too much time being abstract about
      the data-structure, I should have just gone with trees and rolled
      with it}
    The problem is the following: representing recursive data structure
    not as linked data-structures but as a compact representation in a
    binary array. There are various reasons for being interested in such a
    representation:

    \begin{itemize}
    \item if data needs to be serialised and deserialised a lot (for
      instance because it transits on the network) then it can be more
      efficient to manage data in a serialised form (in this we can see
      such a representation as an extension on the idea of \emph{compact
        region}~\cite{yang_compact_2015})
    \item such data representation also has a much smaller memory
      footprint than a linked data structure
      (\citeauthor{vollmer_gibbon_2017} report a $50\%$ to $70\%$
      improvement on binary trees), linked representations are also less
      cache-friendly
    \item in such a data representation, there is no outgoing pointer, so
      the garbage collector is free to treat the entire data structure as
      binary data and not traverse the data
    \end{itemize}

    \Citeauthor{vollmer_gibbon_2017} realise such an implementation scheme
    in a compiler for an \textsc{ml}-like language. Data structures are
    compiled to a compact form, and traversal are transformed in
    destination-passing style~\cite{larus_destination_1998}: building a
    new data-structure is done by writing binary data left-to-right in an
    array. \Citeauthor{vollmer_gibbon_2017}'s compiler targets a typed
    language. With linear types we can represent their type system
    directly in \HaskeLL{}. The challenges are:
    \begin{itemize}
    \item Taking the example of binary trees: we have to traverse the tree
      in a particular order, indeed supposing that the tree is stored as
      its prefix-traversal, the size of the left sub-tree is not known, so
      it is not possible to access the right sub-tree without traversing
      the left sub-tree.
    \item It does not make sense to read from an array of binary data
      until it is fully initialised. After it is initialised, data becomes
      immutable.
    \end{itemize}
    We recognise similar problems to the array-freezing example of
    \fref{sec:freezing-arrays}. However, there are further things to
    consider: first, we cannot freeze a binary array before we have
    completely initialised it, otherwise we would have an incomplete tree,
    which would probably yield a dreaded \texttt{segfault}; also at any
    given point we may have more than one data-structure to fill in (for
    instance both branches of a tree may have yet to be filled) so we need
    to index our arrays by a type-level list\footnote{Haskell has
      type-level lists, which we use in the following. But in any language
      with \textsc{ml}-style polymorphism, the type level list
      $[a_1, …, a_n]$ can be represented by the type
      $(a_1, (…, (a_n,())))$.}

    \todo{copy actual \textsc{api}}
\fi{}}


\subsection{Sockets with type-level state}
\label{sec:sockets}

The \textsc{bsd} socket \textsc{api} is a standard, if not \emph{the}
standard, through which computers connect over networks. It involves a
series of actions which must be performed in order: on the
server-side, a freshly created socket must be \emph{bound} to an
address, then start \emph{listening} incoming traffic, then
\emph{accept} connection requests; said connection is returned as a
new socket, this new socket can now \emph{receive} traffic. One reason
for having that many steps is that the precise sequence of
actions is protocol-dependent. For \textsc{tcp} traffic you would do as
described, but for \textsc{udp}, which does not need connections, you
would not accept a connection but receive messages directly.

The \texttt{socket} library for Haskell, exposes precisely this sequence of
actions.
%
Programming with it is exactly as clumsy as socket libraries for other
languages: after each action, the state of the socket changes, as do the
permissible actions, but these states are invisible in the types.
%
Better is to track the state of sockets in the type, akin to a typestate
analysis~\cite{strom_typestate_1983}.
%
In the |File| \textsc{api} of \fref{sec:io-protocols}, we made files
safer to use at the cost of having to thread a file handle
explicitely: each function consumes a file handle and returns a fresh
one. We can make this cost into an opporunity: we have the option of
returning a handle \emph{with a different type} from that of the
handle we consumed! So by adjoining a phantom type to sockets to track
their state, we can effectively encode the proper sequencing of socket
actions.

As an illustration, we implemented wrapper around the \textsc{api} of the
\texttt{socket} library. For concision, this wrapper is
specialised for the case of \textsc{tcp}.

\begin{code}
data State = Unbound | Bound | Listening | Connected
data Socket (s :: State)
data SocketAddress

socket ::  IOL 1 (Socket Unbound)
bind ::  Socket Unbound ⊸ SocketAddress -> IOL 1 (Socket Bound)
listen :: Socket Bound ⊸ IOL 1 (Socket Listening)
accept ::  Socket Listening ⊸ IOL 1 (Socket Listening, Socket Connected)
connect ::  Socket Unbound ⊸ SocketAddress -> IOL 1 (Socket Connected)
send :: Socket Connected ⊸ ByteString -> IOL 1 (Socket Connected, Unrestricted Int)
receive :: Socket Connected ⊸ IOL 1 (Socket Connected, Unrestricted ByteString)
close :: forall s. Socket s -> IOL ω ()
\end{code}

This linear socket \textsc{api} is very similar to that of files: we use the
|IOL| monad in order to enforce linear use of sockets. The difference
is the argument to |Socket|, which represents the current state of the
socket and is used to limit the functions which apply to a socket
at a given time.


\paragraph{Implementing the linear socket \textsc{api}}
%
Our socket \textsc{api} has been tested by writing a small
echo-server. The \textsc{api} is implemented as a wrapper around the
\texttt{socket} library. Each function wrapped takes half-a-dozen
lines of code, of type annotation and coercions between |IO| and
|IOL|\footnote{Since our implementation of \HaskeLL{} does not yet
  have multiplicity-polymorphism, we had to fake it with type families
  and \textsc{gadts}}. There is no computational behaviour besides
error recovery.

It would have been too restrictive to limit the typestate to enforce
the usage protocol of \textsc{tcp}. We do not intend for a new set of
wrapper functions to be implemented for each protocol. Instead the
wrappers are implemented with a generic type-state evolving according
to the rules of a deterministic automaton. Each protocol can define
it's own automaton, which is represented as a set of instances of
a type class.

\subsection{Pure bindings to impure \textsc{api}s}
\label{sec:spritekit}

In Haskell SpriteKit, \citet{chakravarty_spritekit_2017} have a different kind
of problem. They build a pure interface for graphics, in the same style
as the Elm programming language~\cite{czaplicki_elm_2012}, but implement it in terms
of an existing imperative graphical interface engine.

Basically, the pure interface takes an update function |u : Scene -> Scene| which is
tasked with returning the next state that the screen will display.
%
The scene is first converted to a
pure tree where each node keeps, along with the pure data, a pointer
to its imperative counterpart when it applies, or |Nothing| for new
nodes.
\begin{code}
data Node = Node {payload :: Int, ref :: Maybe (IORef ImperativeNode), children :: [Node]}
\end{code}

On each frame, SpriteKit applies |u| to the current scene, and checks
if a node |n| was updated. If it was, it applies the update directly
onto |ref n| or creates a new imperative node.

Things can go wrong though: if the update function {\em duplicates}
any proxy node, one gets the situation where two nodes |n| and
|n'| can point to the same imperative source |ref n = ref n'|, but
have different payloads. In this situation the |Scene| has become
inconsistent and the behaviour of SpriteKit is unpredictable.

In the {\sc api} of \citet{chakravarty_spritekit_2017}, the burden of checking
non-duplication is on the programmer.  Using linear types, we can
switch that burden to the compiler: we change the update function to
type |Scene ⊸ Scene|, and the |ref| field is made linear too.  Thanks
to linearity, no reference can be duplicated: if a node is copied, the
programmer must choose which one will correspond to the old imperative
counterpart and which will be new.

We implemented such an \textsc{api} in our implementation of
\HaskeLL{}. The library-side code does not use any linear code, the
|Node|s are actually used unrestrictedly. Linearity is only imposed on
the user of the interface, in order to enforced the above restriction.

\section{Related work}
\label{sec:related}

\subsection{Linearity via arrows vs. linearity via kinds}
\label{sec:lin-arrow}

There are two possible choices to indicate the distinction between
linear and unrestricted objects.  Our choice is to use the arrow
type. That is, we have both a linear arrow to introduce linear objects
in the environment, and an unrestricted arrow to introduce
unrestricted objects. This choice is featured in the work of
\citet{mcbride_rig_2016} and \citet{ghica_bounded_2014} and is
ultimately inspired by Girard's presentation of linear logic, which
features only linear arrows, and where the unrestricted arrow $A → B$
is encoded as $!A ⊸ B$.

Another popular choice
\cite{wadler_linear_1990,mazurak_lightweight_2010,morris_best_2016,tov_practical_2011}
is to separate types into two kinds: a linear kind and an unrestricted
kind. Values with a type whose kind is linear are linear, and the
others are unrestricted.  In a typical design making this choice,
every type constructor exists in two flavours: one which constructs a
linear type and one which constructs an unrestricted type. (Thus in
particular such systems feature ``linear arrows'', but they have a
completely different interpretation from ours.) This choice is
attractive on the surface because, intuitively, some types are
inherently linear (file handles, updateable arrays, etc.) and some
types are inherently unrestricted (|Int|, |Bool|, etc.).

%   Two kinds is also more easily compatible with using different
% representations for linear and non-linear values, though this would
% require that the conversion between linear and non-linear type be
% explicit, the sub-kinding of Fo would severely limit this option. At
% any rate, I doubt that this is immensly useful except in DSLs (in
% which it can be highly)

% JP: I think that this is largely orthogonal. Indeed the polymorphism
% of the implementation is only linked to the polymorphism of
% linearity. So this discussion is subsumed by the upcoming discussion
% on polymorphism.

However, after scratching the surface we have discovered that
``linearity via arrows'' has an edge over ``linearity via
kinds'':
\begin{itemize}


\item Better subsumption properties.  When retrofitting linear types
  in an existing language, it is important to share has much code as
  possible between linear and non-linear code. In a system with
  linearity on arrows, the subsumption relation (linear arrows subsume
  unrestricted arrows) and the scaling of context in the application
  rule mean that much linear code can be used as-is from unrestricted
  code, and be properly promoted. Indeed, assuming lists as defined in
  \fref{sec:compatibility} and:
  \begin{code}
    (++) :: [a] ⊸ [a] ⊸ [a]   -- Append two lists
    cycle :: [a] → [a]        -- Repeat a list, infinitely
  \end{code}
  The following definition type-checks, even though |++| is applied to
  unrestricted values and used in an unrestricted context.
  \begin{code}
    f :: [a] → [a] → [a]
    f xs ys = cycle (xs ++ ys)
  \end{code}
  In contrast, in a two-kind system, a function must declare the
  \emph{exact} linearity of its return value. Consequently, to make a
  function promotable from linear to unrestriced, its declaration must
  use polymorphism over kinds. We show how this may look like below;
  but first we need to discuss data types.

  As seen in \fref{sec:programming-intro}, in \HaskeLL{} the reuse of linear
  code extends to data types: the usual parametric data types (lists,
  pairs, etc.) work both with linear and unrestricted values. On the
  contrary, if linearity depends on the kind, then if a linear value
  is contained in a type, the container type must be linear
  too. (Indeed, an unrestricted container could be discarded or
  duplicated, and its contents with it.) Consequently, sharing data
  types also requires polymorphism.  For example, in a two-kinds
  system, the |List| type may look like so, if one assumes a that
  |Type 1| is the kind of linear types and and |Type ω| is the kind of
  unrestricted types.
  \begin{code}
    data List (p :: Multiplicity) (a :: Type p) :: Type p = [] | a : (List l m a)
  \end{code}
  The above declaration ensures that the linearity of the list
  inherits the linearity of the contents. A linearity-polymorphic
  |(++)| function could have the definition, assuming the |(∧)|
  operator takes the minimum of multiplicities.
  \begin{code}
    (++) :: List p (a p) -> List q (a q) -> List (p ∧ q) (a (p ∧ q))
    [] ++ xs = xs
    (x:xs) ++ ys = x : (xs ++ ys)
  \end{code}
  The above type ensures that one can mix multiplicities freely
  between the arguments; but the result must be linear if any argument
  is linear.  However, the definition is valid only if |a q| is a
  subtype of |a (p ∧ q)| for any type family |a :: (p :: Multiplicitiy) ->
  Type p|. Thus, code-sharing requires not only polymorphism, but a
  non-trivial subtyping and subkinding system.

  Note that, in the above, we parameterize over multiplicities instead
  of parameterizing over kinds directly, as is customary in the
  literature. We do so because it fits better \ghc{}, whose kinds are
  already parameterized over a so-called
  levity~\cite{eisenberg_levity_2017}.


\item 
  % It is easy to extend our system to any set of
  % ground multiplicities with a ring structure
  % (\fref{sec:extending-multiplicities}).
  % In contrast,
  % in a multiple-kind system, such extensions require \textit{ad-hoc}
  % support. Indeed, affine types require changes in the subkinding
  % system, which in turns may impact unification.
  % JP: I do not think that this is true with the |Type p| view.
  Linearity on the arrow meshes better with dependent
  types (see \fref{sec:extending-multiplicities}).  Indeed, consider a typical predicate over
  files (|P : File → ∗|). It will need to mention its argument several
  times to relate the file at the start and at the start of a sequence
  of operations. While this is not a problem in our system, the
  function |P| is not expressible if |File| is intrinsically
  linear. Leaving the door open to dependent types is crucial to us,
  as this is currently explored as a possible extension to \ghc{}.

% Linearity-on-arrow makes it possible to constrain any function to
% use its arguments linearly, this is useful for the function writer,
% similarly to how parametricity can be. We also anticipate that we
% can leverage programmers’ annotation to make linear functions always
% inlinable.

% JP: isn't so also for a kinding system?

  % We also anticipate that we can leverage programmers’ annotation to
  % make linear functions always inlinable.

  % JP: probably not an
  % advantage; the same can be done with kinds, probably. I believe
  % the tradeoff is between unique/linear.

  % We have applications where we implement something using unsafe
  % primitive that are not linear we expose a safe API where the user
  % has to use linear function. I don’t know how we could do the same
  % using a two-kind system.
  % JP: I do not understand this one.

% \item Easier implementation. We managed to implement a working prototype of
%   \textsc{ghc}, linearity-on-arrow, with reasonable effort. We attribute its
%   relative simplicity to two factors.  First, we avoided tracking of the
%   kind of types in the variables, which is a daunting task in \textsc{ghc}'s
%   type-checker \jp{why?}.

%   Second, \textsc{ghc} already supports impredicative dependent types
%   and a wealth of unboxed or otherwise primitive types and kinds that
%   cannot be substituted for polymorphic type arguments. Further extending
%   the kind system is a complex endeavour which we could avoid entirely.

%   JP: Probably, the implementation burden *itself* can be kept under
%   control thanks this kind of polymorphism (see Simon's email):
%   TYPE : Linearity -> KIND

\end{itemize}

An advantage of ``linearity via kinds'' is the possibility to directly
declare the linearity of values returned by a function---not just that
of the argument of a function. In contrast, in our system if one wants
to indicate that a returned value is linear, we have to
use a double-negation trick. That is, given $f : A → (B ⊸ !r) ⊸ r$,
then $B$ can be used a single time in the (single) continuation, and
effectively $f$ ``returns'' a single $B$. One can obviously declare a
type for linear values |Linear a = (a ⊸ !r) ⊸ r| and chain
|Linear|-returning functions with appropriate combinators.  In fact,
as explained in \fref{sec:linear-io}, the cost of the double negation
almost entirely vanishes in the presence of an ambient monad.
\info{Actually linearity via kids works well with lazy evaluation. We only need a ``linear unit type'' (which is like a type of effects).
All linear things will eventually accrete in such a type and it
can collected for example in $runEffect :: LinearUnit -o IO ()$; or we could have $main :: LinearUnit$.
One may also need an $Unrestrited$ in this system if one wants to locally escape linearity.
}

\subsection{Other variants of ``linearity on the arrow''}
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
results in the judgement $⊢_ω λx. (x,x) : A ⊸ (A,A)$ being derivable.
%
This derivation is not desirable: it implies that there cannot be
reusable definitions of linear functions. In terms of linear logic~\cite{girard_linear_1987},
\citeauthor{mcbride_rig_2016} makes the natural function of type $!(A⊸B) ⟹ !A⊸!B$
into an isomorphism.
In that respect, our system is closer to
\citeauthor{ghica_bounded_2014}'s.

The essential differences between our system and that of
\citeauthor{ghica_bounded_2014} is that we support
multiplicity-polymorphism and datatypes. In particular our |case| rule
is novel.

% What we keep from
% \citeauthor{mcbride_rig_2016}, is the typing rule of |case| (see
% \fref{sec:statics})
% JP: nope, there is no 'case' rule in mcbride_rig_2016

The literature on so-called
coeffects~\cite{petricek_coeffects_2013,brunel_coeffect_core_2014}
uses type systems similar to \citeauthor{ghica_bounded_2014}, but
with a linear arrow and multiplicities carried by the exponential
modality instead. \Citet{brunel_coeffect_core_2014}, in particular,
develops a Krivine-style realisability model for such a calculus. We are not
aware of an account of Krivine realisability for lazy languages, hence
this work is not directly applicable to \calc.

\subsection{Uniqueness and ownership typing}
\label{sec:uniqueness}

The literature
% is awash with enforcing linearity not via linear types,
contains many proposals for uniqueness (or ownership) types (in contrast with
linear types).
Prominent representative languages with uniqueness types include
Clean~\cite{barendsen_uniqueness_1993} and
Rust~\cite{matsakis_rust_2014}. \HaskeLL, on the other hand, is
designed around linear types based on linear
logic~\cite{girard_linear_1987}.

Linear types and uniqueness types are, at their core, dual: whereas a linear type is
a contract that a function uses its argument exactly once
even if the call's context can share a linear argument as many times as it
pleases, a uniqueness type ensures that the argument of a function is
not used anywhere else in the expression's context even if the callee
can work with the argument as it pleases.
%
Seen as a system of constraints, uniqueness typing is a {\em non-aliasing
analysis} while linear typing provides a {\em cardinality analysis}. The
former aims at in-place updates and related optimisations, the latter
at inlining and fusion. Rust and Clean largely explore the
consequences of uniqueness on in-place update; an in-depth exploration
of linear types in relation with fusion can be found
in~\citet{bernardy_composable_2015};
see also the discussion in \fref{sec:fusion}.

Because of this weak duality, we could have
retrofitted uniqueness types to Haskell. But several points
guided our choice of designing \HaskeLL{} around linear
logic rather than uniqueness types: (a) functional languages have more use
for fusion than in-place update (if the fact that \textsc{ghc} has a cardinality
analysis but no non-aliasing analysis is any indication); (b) there is a
wealth of literature detailing the applications of linear
logic — see \fref{sec:applications}; (c) and decisively, linear type systems are
conceptually simpler than uniqueness type systems, giving a
clearer path to implementation in \textsc{ghc}.

\paragraph{Rust \& Borrowing}
% aspiwack: most of this looks irrelevant at this stage
%
% Rust \cite{matsakis_rust_2014} features a variant of uniquness typing, called
% ownership typing. Like the original formulation of linear logic, in Rust, if a
% type \texttt{T} stands for linear values, \Red{which are copied on function
%   calls}, unrestricted values are denoted \texttt{RC<T>}, and duplication is
% explicit.
% %
% \jp{It is not clear why this applies to Rust only and not other uniqueness typing systems.}
% Rust addresses the problem of being mindful about
% memory, resources, and latency, but this comes at a price: Rust,
% as a programming language, is specifically optimised for writing
% programs that are structured using the ``RAII''
% pattern\footnote{Resource Acquisition Is Initialization: \url{https://en.wikipedia.org/wiki/Resource_acquisition_is_initialization}}
% (where resource lifetimes are tied directly or indirectly to stack
% allocated objects that are freed when the control flow exits the
% current lexical scope). Ordinary functional programs seldom fit this
% particular resource acquisition pattern so end up being second class
% citizens. For instance, tail-call optimization, crucial to the
% operational behaviour of many functional programs, is not usually
% sound. This is because resource liberation must be triggered when the
% tail call returns.
% %
% \HaskeLL{} aims to hit a different point in the design space where
% regular non-linear expressions are the norm, yet
% % gracefully scaling up
% investing extra effort to enforce invariants or perform low-level
% systems programming, with control over resources and latency, is still possible.

In \HaskeLL{} we need to thread linear variables throughout the
program (consider using several functions of type |T ⊸ T|).  Even
though this burdend could be alleviated using syntactic sugar, Rust uses
instead a type-system feature for this purpose: \emph{borrowing}.

% If \texttt{T} is the type of some owned value, \texttt{\&T} is the
% type of a borrowed value of type \texttt{T}.

% JP: This notion is not used later.
Borrowed values differ from owned values in that they can
be used in an unrestricted fashion, albeit in a \emph{delimited
  life-time}\jp{is this time dynamic or static? If static it should be
  `scope' --- aspiwack: the lifetime is statically scoped in this case}.

Borrowing does not come without a cost, however: if a
function \texttt{f} borrows a value \texttt{v} of type \texttt{T},
then the caller of the function \emph{must} retain \texttt{v} alive
until \texttt{f} has returned; the consequence is that Rust cannot, in
general, perform tail-call elimination, crucial to the operation
behaviour of many functional programs, as some resources must be
released \emph{after} \texttt{f} has returned.

The reason that Rust programs depend so much on borrowing is that
unique values are the default. \HaskeLL{} aims to hit a different
point in the design space where regular non-linear expressions are the
norm, yet gracefully scaling up investing extra effort to enforce
linearity invariants is possible.
% Therefore, threading linear variable, being much less common, will not be as painful.
% JP: but the reader we don't care; the focus here is on the linear
% bits. Let not make excuses.
Nevertheless, we discuss in \fref{sec:extending-multiplicities} how to
extend \HaskeLL{} with borrowing.

% aspiwack: also not too relevant in the current state of the paper
%
% \paragraph{Borrowing references in data structures}
% In an imperative language, one often walks data structure, extract
% references and pass them around. In Rust, the borrowing system
% ensures that the passed reference does not outlive the datastructure
% that it points to.

% In a functional language, instead of extracting references, one will
% use lenses to lift a modification function from a local subtree to a
% global one. Thanks to garbage collection, there is already no risk of
% dangling references, but one has to pay a runtime cost. By using
% linear types one can avoid this cost.

% Indeed, we can ensure that a modification function can have the type:
% |Reference ⊸ Reference| and thus can be implemented with no need for
% GC. At the same time, the lens library will use linear types and lift
% local linear modifications to global linear modifications. Note that,
% if the original object lives in the GC heap (and thus can be shared),
% the same lens library can be used, but individual lifting of
% modifications cannot be implemented by in-place update.
% \rn{Is this text stale?  That is, from an earlier version of the paper that talked
%   about the ``GC heap''?}


\subsection{Linearity via monads}

\citet{launchbury_st_1995} taught us
a conceptually simple approach to lifetimes: the |ST| monad. It has
a phantom type parameter |s| (the \emph{region}) that is instantiated once at the
beginning of the computation by a |runST| function of type:
\begin{code}
  runST :: (forall s. ST s a) -> a
\end{code}
This way, resources that are allocated during the computation, such
as mutable cell references, cannot escape the dynamic scope of the call
to |runST| because they are themselves tagged with the same phantom
type parameter.

\paragraph{Region-types}

With region-types such as |ST|, we cannot express typestates, but this
is sufficient to offer a safe \textsc{api} for freezing array or
ensuring that files are eventually closed.
This simplicity (one only needs rank-2 polymorphism)
comes at a cost: we've already mentionned in
\fref{sec:freezing-arrays} that it forces operations to be more
sequentialised than need be, but more importantly, it does not
support \emph{prima facie} the interaction of nested regions.

\citet{kiselyov_regions_2008} show that it is possible to promote
resources in parent regions to resources in a subregion. But this is
an explicit and monadic operation, forcing an unnatural imperative
style of programming where order of evaluation is explicit.
The HaskellR project~\cite{boespflug_project_2014} uses monadic
regions in the style of \citeauthor{kiselyov_regions_2008} to safely
synchronise values shared between two different garbage collectors for
two different languages. \Citeauthor{boespflug_project_2014} report
that custom monads make writing code at an interactive prompt
difficult, compromises code reuse, forces otherwise pure functions to
be written monadically and rules out useful syntactic facilities like
view patterns.

In contrast, with linear types, values in two regions hence can safely
be mixed: elements can be moved from one data structure (or heap) to
another, linearly, with responsibility for deallocation transferred
along.


\paragraph{Idris's dependent indexed monad}
%
To go beyond simple regions, Idris introduces  a generic way to add typestate on top of a monad, the
|ST| indexed monad transformer\footnote{See \eg
  \url{http://docs.idris-lang.org/en/latest/st/index.html}. Where you
  will also discover that |ST| is actually defined in terms of a more
  primitive |STrans|}. The basic
idea is that everything which must be single-threaded~--~and that we
would track with linearity~--~become part of the state of the
monad. For instance, coming back to the sockets of \fref{sec:sockets},
the type of |bind| would be as follows:
\begin{code}
  bind :: (sock :: Var) -> SocketAddress -> ST IO () [sock ::: Socket Unbound :-> Socket Bound]
\end{code}
Where |sock| is a reference into the monads's state, and |Socket Unbound| is
the type of |sock| before |bind|, and |Socket Bound|, the type of
|sock| after |bind|.

Idris uses its dependent types to associate a state to the value of
its first argument. Dependent types are put to even greater use for
error management where the state of the socket depends on whether
|bind| succeeded or not:
\begin{code}
  -- In Idris, |bind| uses a type-level function (|or|) to handle errors
  bind ::  (sock :: Var) -> SocketAddress ->
           ST IO (Either () ()) [sock ::: Sock Unbound :-> (Sock Bound `or` Sock Unbound)]
  -- In \HaskeLL{}, by contrast, the typestate is part of the return type
  bind :: Socket Unbound ⊸ SocketAddress -> Either (Socket Bound) (Socket Unbound)
\end{code}
%
The support for dependent types in \textsc{ghc} is not as
comprehensive as Idris's. But it is conceivable to implement such an
indexed monad transformer in Haskell. However, this is not an easy task,
and we can anticipate that the error messages would be hard to stomach.

% \subsection{Operational aspects of linear languages}

% \unsure{This section will need a clean up, to be more in phase of what
% we present in the evaluation section}

% \Citet{wakeling_linearity_1991} produced a complete implementation of
% a language with linear types, with the goal of improving 
% performance. Their implementation features a separate linear heap, as
% \fref{appendix:dynamics} where they allocate as much as possible in the
% linear heap, as modelled by the strengthened semantics. However,
% \citeauthor{wakeling_linearity_1991} did not obtain
% consistent performance gains. On the other hand, they still manage to
% reduce \textsc{gc} usage, which may be critical in distributed and
% real-time environments, where latency that matters more than
% throughput.

% \citeauthor{wakeling_linearity_1991} propose to {\em not} attempt prompt freeing of
% thunks; they only taking advantage of linearity for managing the lifetimes of
% large arrays. Our approach is similar: we advocate exploiting linearity for
% operational gains on large data structures (but not just arrays) stored
% off-heap. We go further and leave the management of external (linear) data to
% external code, only accessing it via an \textsc{api}. Yet, our language supports
% an implementation where each individual constructor with multiplicity 1 can be
% allocated on a linear heap, and deallocated when it is pattern matched.
% Implementing this behaviour is left for future work.

% \subsubsection{Garbage}
% \citet{mogensen_types_1997} proposes a type system whose purpose is to
% track the number of times that a value is used. They intend their
% system to be used for inference instead of declaration. Thus, while
% our main concern is the smooth integration with an existing lazy
% functional language, they are not concerned with language design issues.
% %
% Besides, their system features both annotations on types
% an certain variable bindings; while our type-system is related to
% theirs it appears to be incomparable.

% The work of \citet{igarashi_garbage_2000} uses the typesystem of
% Mogensen to drive a garbage collection mechanism. Yet, their approach
% is opposite to ours: while we aim to keep linear values
% completely outside of garbage collection, they use the type
% information at runtime to ensure that the GC does not follow dangling
% pointers.
% % JP: How can that even work?



\section{Future work}

\subsection{Controlling program optimisations}
\label{sec:fusion}
Inlining is a cornerstone of program optimisation, exposing
opportunities for many program transformations. Yet not every function can
be inlined without negative effects on performance: inlining a
function with more than one use sites of the argument may result in
duplicating a computation. For example one should avoid the following
reduction: |(\x -> x ++ x ) expensive ⟶ expensive ++ expensive|.

Many compilers can discover safe inlining opportunities by analysing
source code and determine how many times functions use their
arguments.  (In \textsc{ghc} this analysis is called a cardinality
analysis~\cite{sergey_cardinality_2014}). A limitation of such an
analysis is that it is necessarily heuristic (the problem is
undecidable for Haskell). Because inlining is crucial to efficiency, programmers
find themselves in the uncomfortable position of relying on a
heuristic to obtain efficient programs. Consequently, a small, seemingly
innocuous change can prevent a critical inlining opportunity and have
rippling catastrophic effects throughout the program.
Such unpredictable behaviour justifies the folklore that high-level languages should be
abandoned to gain precise control over program efficiency.
%% Do not delete the above sentence without discussion.

A remedy is to use the multiplicity annotations of \calc{} as
cardinality \emph{declarations}. Formalising and implementing the
integration of multiplicity annotations in the cardinality analysis is
left as future work.

Another important optimisation for lazy languages is full-laziness,
which attempt to maximize sharing of sub-expressions. Unfortunately,
full-laziness is sometimes a pessimisation, as in the following example,
which is a simplified version of an issue that occurs in
practice with Haskell code\footnote{see http://www.well-typed.com/blog/2016/09/sharing-conduit/}:
\begin{code}
main = forM_ [1..5] (\i -> mapM_ print [1 .. N])
\end{code}
If |mapM_| is not inlined, then full-laziness transforms the above into
\begin{code}
main = let xs = [1 .. N] in forM_ [1..5]  (\i -> mapM_ print xs)
\end{code}
Even though one would expect the above program to use constant space
(because the list |[1..N]| is produced lazily), when the intermediate
list |[1..N]| is shared between runs of |mapM_ print [1 .. N]|, the
memory residency becomes proportional to |N|. We conjecture
that linearity annotations can be used to guide full-laziness:
arguments to linear functions should not be shared. Indeed, being used
only once, it always is more memory-efficient to re-create them at
each invokation. In this case, if |mapM_| is given the type |(a ⊸ IO
b) -> [a] ⊸ IO ()|, the compiler would see that sharing of |[1..N]|
should be avoided.

\subsection{Extending multiplicities}
\label{sec:extending-multiplicities}

For the sake of this article, we use only multiplicities
$1$ and $ω$.  But in fact \calc{} can readily be extended to
more, following \citet{ghica_bounded_2014} and
\citet{mcbride_rig_2016}. The general setting for \calc{} is an
ordered-semiring of multiplicities (with a join operation for type
inference).  In particular, in order to support dependent types, we
additionally need a $0$ multiplicity. We may may want to add a
multiplicity for affine arguments (\ie  arguments which can be
used \emph{at most once}).

The typing rules are mostly unchanged with the \emph{caveat} that
$\mathsf{case}_π$ must exclude $π=0$ (in particular we see that we
cannot substitute multiplicity variables by $0$). The variable rule becomes:
$$
\inferrule{ x :_1 A \leqslant Γ }{Γ ⊢ x : A}
$$
Where the order on contexts is the point-wise extension of the order
on multiplicities.

In \fref{sec:uniqueness}, we have considered the notion of
\emph{borrowing}: delimiting life-time without restricting to linear
usage. This seems to be a useful pattern, and we believe it can be
encoded as an additional multiplicity as follows: let $β$ be an
additional multiplicity with the following characteristics:
\begin{itemize}
\item $1 < β < ω$
\item $β+β = 1+β = 0+β = 1+1 = β$
\end{itemize}
That is, $β$ supports contraction and weakening but is smaller than
$ω$. We can then introduce a value with an explicit lifetime with the
following pattern
\begin{code}
  borrow :: (T -> _ β Unrestricted a) -> _ β Unrestricted a
\end{code}
The |borrow| function makes the life-time manifest in the structure of
the program. In particular, it is clear that calls within the argument
of |borrow| are not tail: a shortcoming of borrowing that we mentioned
in \fref{sec:uniqueness}.

\subsection{Future industrial applications}
\label{sec:industry}
\manuel{Hard to understand.}
Our own work in an industrial context triggered our efforts to add
linear types to \textsc{ghc}. We were originally motivated by
precisely typed protocols for complex interactions and by taming
\textsc{gc} latencies in distributed systems. But we have since
noticed other potential applications of linearity in a variety of
other industrial projects.

\begin{description}

\item[Interface to communication channels] Many real-world
  applications interface with communications channels (including
  sockets, but also file logs, etc.).  It is so tempting for
  functional programmers to give a non-monadic interface to such
  channels that programmers give in (see \eg the \texttt{streaming}
  library for Haskell or \cite{lippmeier_parallel_2016}). Thus an
  external channel may be accessible using a value of type |Stream
  a|. Unfortunately, when maintaining complex programs it is easy to
  unknowingly pass two copies of a stream to different functions which
  compete for access to the channel.  We have encountered such
  mistaken duplications in industrial projects, where they produce
  bugs which are painful to track down. A linear type discipline would
  prevent such bugs from happening.


\item[Programming foreign heaps] Complex projects with large teams
  invariably involve a mix of programming languages. Reusing legacy
  code is often much cheaper than reimplementing it. A key to
  successful interoperation between languages is performance. If all
  code lives in the same address space, then data need not be copied
  as it flows from function to function implemented in multiple
  programming languages. Trouble is, language A needs to tell language
  B what objects in language A's heap still have live references in
  the call stack of language B to avoid too eager garbage collection.

  For instance, users of \texttt{inline-java} call the \textsc{JVM}
  from Haskell via the \textsc{JNI}. The \textsc{JVM} implicitly
  creates so-called \emph{local references} any time we request a Java
  object from the \textsc{JVM}. The references count as \textsc{GC}
  roots that prevent eager garbage collection. For performance, local
  references have a restricted scope: they are purely thread-local and
  never survive the call frame in which they were created. Both
  restrictions to their use can be enforced with linear types.

\item[Remote direct memory access]
  \Fref{sec:cursors} is an example of an \textsc{api} requiring
  destination-passing style. This style often appears
  in performance-sensitive contexts. One notable example from our
  industrial experience is \textsc{rdma} (Remote Direct Memory Access),
  which enables machines in high-performance clusters to copy data
  from the address space in one process to that of a remote process
  directly, bypassing the kernel and even the
  \textsc{cpu}, thereby avoiding any unnedded copy in the process.

  One could treat a remote memory location as a low-level resource, to
  be accessed using an imperative {\sc api}. Using linear types, one
  can instead treat it as a high-level value which can be written to
  directly (but exactly once). Using linear types the compiler can
  ensure that, as soon as the writing operation is complete, the
  destination computer is notified.
\end{description}



\section{Conclusions}

This article demonstrates how an existing lazy language, such
as Haskell, can be extended with linear types, without compromising
the language, in the sense that:
\begin{itemize}
\item existing programs are valid in the extended language
  \emph{without modification},
\item such programs retain the same operational semantics, and in particular
\item the performance of existing programs is not affected,
\item yet existing library functions can be reused to serve the
  objectives of resource-sensitive programs with simple changes to
  their types, and no code duplication.
\end{itemize}
In other words: regular Haskell comes first. Additionally, first-order
linearly typed functions and data structures are usable directly from
regular Haskell code. In such a setting their semantics is that of
the same code with linearity erased.

\HaskeLL{} was engineered as an unintrusive design, making it tractable
to integrate to an existing, mature compiler with a large ecosystem.
We have developed a prototype implementation extending
\textsc{ghc} with multiplicities. As we hoped, this
design integrates well in \textsc{ghc}.

Even though we change only \ghc's type system, we found that the
compiler and runtime already had the features necessary for unboxed,
off-heap, and in-place data structures.  That is, \ghc{} has the
low-level compiler primitives and \textsc{ffi} support to implement,
for example, mutable arrays, mutable cursors into serialised data, or
off-heap foreign data structures without garbage collection.  These
features could be used {\em before} this work, but their correct use
put some burden-of-proof on the programmers. Linearity unlocks these
capabilities for safe, compiler-checked use, within pure code.




%% Acknowledgments
\begin{acks}                            %% acks environment is optional
                                        %% contents suppressed with 'anonymous'
  %% Commands \grantsponsor{<sponsorID>}{<name>}{<url>} and
  %% \grantnum[<url>]{<sponsorID>}{<number>} should be used to
  %% acknowledge financial support and will be used by metadata
  %% extraction tools.
  This work has received funding from the European Commission
  through the SAGE project (grant agreement no. 671500).
  We thank Manuel Chakravarty, Stephen Dolan and Peter Thiemann for their valuable
  feedback on early versions of this paper.
\end{acks}

%% Bibliography
\bibliography{../PaperTools/bibtex/jp,../local}{}


%% Appendix
\appendix
\section{Semantics and soundness of \calc{}}
\label{appendix:dynamics}

\newcommand{\termsOf}[1]{\mathnormal{terms}(#1)}
\newcommand{\multiplicatedTypes}[1]{\bigotimes(#1)}
\newcommand{\ta}[2]{γ(#1)(#2)}

In accordance with our stated goals in \fref{sec:introduction}, we are
interested in two key properties of our system: 1. that we can implement
a linear \textsc{api} with mutation under the hood, while exposing a
pure interface, and 2. that typestates are indeed enforced.

We introduce two dynamic semantics for \calc{}: a semantics with
mutation which models the implementation but blocks on incorrect
type-states, and a pure semantics, which we dub \emph{denotational} as
it represents the intended meaning of the program. We consider here array
primitives in the style of \fref{sec:freezing-arrays}, but we could extend to
any number of other examples such as the files of
\fref{sec:io-protocols}.

We prove the two semantics bisimilar, so that type-safety and progress
can be transported from the denotational semantics to the ordinary
semantics with mutation. The bisimilarity itself ensures that the
mutations are not observable and that the semantics is correct in exposing
a pure semantics. The progress result proves that typestates need not be
tracked dynamically.

\subsection{Preliminaries}

Our operational semantics are big-step semantics with laziness in the
style of \citet{launchbury_natural_1993}. In such semantics, sharing
is expressed by mutating the environment assigning value to
variables. Terms are transformed ahead of execution in order to
reflect the amount of sharing that a language like Haskell would
offer. In particular the arguments of an application are always
variables.

Following \citet{gunter_partial-big-step_1993}, however, we consider
not only standard big-step derivations but also partial derivations.
The reason to consider partial derivation is that they make it
possible to express properties such as \emph{progress}: all partial
derivations can be extended.

Given a number of rules defining $a⇓b$ with ordered premises (we will
use the ordering of premises shortly), we
define a \emph{total derivation} of $a⇓b$ as a tree in the standard
fashion. As usual $a⇓b$ holds if there is a total derivation for it.
A \emph{partial} derivation of $a⇓?$ (the question mark is part of the
syntax: the right-hand value is the result of the evaluation, it is
not yet known for a partial derivation!) is either:
\begin{itemize}
\item just a root labelled with $a⇓?$,
\item or an application of a rule matching $a$ where exactly one of
  the premises, $a'⇓?$ has a partial derivation, all the premises to
  the left of $a'⇓?$ have a total derivation, and the premises to the
  right of $a'⇓?$ are not known yet (since we would need to know the
  value $?$ to know what the root of the next premise is).
\end{itemize}

Remark that, by definition, in a partial derivation, there is exactly one
$b⇓?$ with no sub-derivation. Let us call $b$ the \emph{head} of the
partial derivation. And let us write $a⇓^*b$ for the relation which
holds when $b$ is the head of some partial derivation with root
$a⇓?$. We call $a⇓^*b$ the \emph{partial evaluation relation}, and, by
contrast, $a⇓b$ is sometimes referred to as the the \emph{complete
  evaluation relation}.

\subsection{Ordinary semantics}

Our semantics, which we often call \emph{ordinary} to constrast it
with the denotational semantics of \fref{sec:denotational}, follows
closely the semantics of \citet{launchbury_natural_1993}. The main
differences are that we keep the type annotation, and that we have
primitives for proper mutation.

Mixing mutation and laziness is not usual, as the unspecified
evaluation order of lazy languages would make mutation order
unpredicable, hence programs non-deterministic. It is our goal to show
that the linear typing discipline ensures that, despite the mutations,
the evaluation is pure.

Just like \citet{launchbury_natural_1993} does, we constrain the terms
to be explicit about sharing, before any evaluation takes
place. \Fref{fig:launchbury:syntax} shows the translation of abtrary
term to terms in the explicit-sharing form.

\begin{figure}
  \figuresection{Translation of typed terms}
  \begin{align*}
    (λ_π(x{:}A). t)^* &= λ_π(x{:}A). (t)^* \\
    x^*             &= x \\
    (t  x )^*     &= (t)^*  x \\
    (t  u )^*     &= \flet[π] y : A = (u)^* \fin (t)^*  y &
    \text{with $Γ⊢ t : A →_π B$}
  \end{align*}
  \begin{align*}
    c_k  t₁ … t_n   &= \flet x₁ :_{π_1} A_1 = (t₁)^*,…, x_n :_{π_n} A_n = (t_n)^*
                      \fin c_k x₁ … x_n & \text{with $c_k : A_1
                                          →_{π_1}…A_n →_{π_n}D$}
  \end{align*}
  \begin{align*}
    (\case[π] t {c_k  x₁ … x_{n_k} → u_k})^* &= \case[π] {(t)^*} {c_k  x₁ … x_{n_k} → (u_k)^*} \\
    (\flet[π] x_1: A_1= t₁  …  x_n : A_n = t_n \fin u)^* & = \flet[π] x₁:A_1 = (t₁)^*,…, x_n:A_n= (t_n)^* \fin (u)^*
  \end{align*}

  \caption{Syntax for the Launchbury-style semantics}
  \label{fig:launchbury:syntax}
\end{figure}

The evaluation relation is of the form $Γ : e ⇓ Δ : z$ where $e$ is an
expression, $z$ a value $Γ$ and $Δ$ are \emph{environments} with
bindings of the form $x :_ω A = e$ assigning the expression $e$ the the
variable $x$ of type $A$. Compared to the pure semantic of
\citeauthor{launchbury_natural_1993}, we have one additional kind of
values, $l$ for names of arrays. Array names are given semantics by
additional bindings in environments which we write, suggestively, $l
:_1 A = arr$. The $1$ is here to remind us that arrays cannot be used
arbitrarily, however, it does not mean they are always used in a
linear fashion: frozen arrays are not necessarily linear, but they
still appear as array names.

The details of the ordinary evaluation relation are given in
\fref{fig:dynamics}. Let us describe the noteworthy rules:
\begin{description}
\item[mutable cell] array names are values, hence are not
  reduced. In that they differ from variables.
\item[newMArray] allocates a fresh array of the given size (we write
  $i$ for an integer value). Note that
  the value of $a$ is not evaluated: an array in the environment is
  a concrete list of (not necessarily distinct) variables.
\item[writeArray] Mutates its array argument
\item[freezeArray] Mutates \emph{the type} of its argument to |Array|
  before wrapping it in $\varid{Unrestricted}$, so that we cannot call
  $\varid{write}$ on it anymore: $\varid{write}$ would block because
  the type of $l$ is not |MArray|. Of course, in an implementation
  this would not be checked because progress ensures that the case
  never arises.
\end{description}

\begin{figure}
  \begin{mathpar}
    \inferrule{ }{Γ : λp. t ⇓ Γ : λp. t}\text{m.abs}


    \inferrule{Γ : e ⇓ Δ : λp.e' \\ Δ : e'[π/q] ⇓ Θ : z} {Γ :
      e π ⇓ Θ : z} \text{m.app}

    \inferrule{ }{Γ : λ_π(x{:}A). e ⇓ Γ : λ_π(x{:}A). e}\text{abs}


    \inferrule{Γ : e ⇓ Δ : λ_π(y{:}A).e' \\ Δ : e'[x/y] ⇓ Θ : z} {Γ :
      e x ⇓ Θ : z} \text{application}

    \inferrule{Γ : e ⇓ Δ : z}{(Γ,x :_ω A = e) : x ⇓ (Δ;x :_ω A = z) :
      z}\text{variable}

    \inferrule{ }
    {(Γ,l :_1 A = arr) : l ⇓ (Γ, l :_1 A = arr) : l}\text{mutable cell}

    \inferrule{(Γ,x_1 :_ω A_1 = e_1,…,x_n :_ω A_n e_n) : e ⇓ Δ : z}
    {Γ : \flet[π] x₁ : A_1 = e₁ … x_n : A_n = e_n \fin e ⇓ Δ :
      z}\text{let}

    \inferrule{ }{Γ : c  x₁ … x_n ⇓ Γ : c  x₁ …
      x_n}\text{constructor}


    \inferrule{Γ: e ⇓ Δ : c_k  x₁ … x_n \\ Δ : e_k[x_i/y_i] ⇓ Θ : z}
    {Γ : \case[π] e {c_k  y₁ … y_n ↦ e_k } ⇓ Θ : z}\text{case}

    %%%% Arrays

    \inferrule
    {Γ:n ⇓ Δ:i \\ (Δ, l :_1 \varid{MArray}~a = [a,…,a]) : \flet[1] x = l \fin f~x ⇓ Θ : \varid{Unrestricted}~x}
    {Γ : \varid{newMArray}~n~a~f ⇓ Θ : \varid{Unrestricted}~x}\text{newMArray}

    \inferrule{Γ:n⇓Δ:i \\ Δ:arr ⇓ (Θ,l:_1 \varid{MArray}~a = [a_1,…,a_i,…,a_n]):l}
    {Γ : \varid{write}~arr~n~a ⇓ Θ,l :_1 \varid{MArray}~a =
      [a_1,…,a,…,a_n] : l}\text{write}

    \inferrule{Γ:arr ⇓ (Δ,l :_1 \varid{MArray}~a = [a_1,…,a_n]):l}
    { Γ : \varid{freeze}~arr ⇓ (Δ,l :_1 \varid{Array}~a = [a_1,…,a_n],
      x :_ω \varid{Array}~a = l) :
      \varid{Unrestricted}~x}\text{freeze}

    \inferrule
    {Γ : n ⇓ Δ : i \\ Δ:arr ⇓ (Θ,l :_1 \varid{Array}~a =
      [a_1,…,a_i,…,a_n]) : l \\ (Θ,l :_1 \varid{Array}~a =
      [a_1,…,a_i,…,a_n]) : a_i ⇓ Λ : z}
    {Γ : \varid{read}~arr~n ⇓ Λ : z}

    %%%% /Arrays
  \end{mathpar}

  \caption{Ordinary dynamic semantics}
  \label{fig:dynamics}
\end{figure}

\subsection{Denotational semantics}
\label{sec:denotational}

\begin{figure}
  \begin{mathpar}
\inferrule{ }{Ξ ⊢ (Γ || λp. t ⇓ Γ || λp. t) :_ρ A, Σ}\text{m.abs}

\inferrule{Ξ ⊢ (Γ || e ⇓ Δ || λp.e') :_ρ A, Σ \\ Ξ ⊢ (Δ || e'[π/q] ⇓ Θ || z) :_ρ A, Σ} {(Γ :
  e π ⇓ Θ : z) :_ρ A, Σ} \text{m.app}

\inferrule{ }{Ξ ⊢ (Γ || λ_π(x{:}A). e ⇓ Γ || λ_π (x{:}A). e) :_ρ A→_π B, Σ}\text{abs}

\inferrule
    {Ξ  ⊢  (Γ||e      ⇓ Δ||λ(y:_π A).u):_ρ A →_π B, x:_{πρ} A, Σ \\
     Ξ  ⊢  (Δ||u[x/y] ⇓ Θ||z)   :_ρ       B,            Σ}
    {Ξ  ⊢  (Γ||e x ⇓ Θ||z) :_ρ B ,Σ}
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
  {Ξ ⊢ (Γ,       x_1 :_{ρπ} A_1 = e_1 … x_n :_{ρπ} A_n = e_n  ||  t ⇓ Δ||z) :_ρ C, Σ}
  {Ξ ⊢ (Γ||\flet[π] x_1 :  A_1 = e_1 … x_n : A_n = e_n \fin t ⇓ Δ||z) :_ρ C, Σ}
{\text{let}}

\inferrule
  { }
  {Ξ ⊢ (Γ || c x_1…x_n  ⇓ Γ || c x_1…x_n) :_ρ A, Σ}
{\text{constructor}}

\inferrule
  {Ξ,y_1:_{π_1qρ} A_1 … ,y_n:_{π_nqρ} A_n ⊢ (Γ||e ⇓ Δ||c_k x_1…x_n) :_{πρ} D, u_k:_ρ C, Σ \\
    Ξ ⊢ (Δ||u_k[x_i/y_i] ⇓ Θ||z) :_ρ C, Σ}
  {Ξ ⊢ (Γ||\case[π] e {c_k y_1…y_n ↦ u_k} ⇓ Θ||z) :_ρ C, Σ}
  {\text{case}}

%%%%% Arrays

\inferrule
{Ξ ⊢ (Γ||n ⇓ Δ||i), \varid{Int}, (arr:_ρ \varid{MArray}~a, Σ) \\ Ξ ⊢
  (Δ||\flet[1] x = [a,…,a] \fin f~x) ⇓ Θ||\varid{Unrestricted}~x) :_1 \varid{Unrestricted}~B, Σ}
{Ξ ⊢ (Γ||\varid{newMArray}~n~a~f ⇓ Θ||\varid{Unrestricted}~x) :_ρ \varid{Unrestricted}~B, Σ}\text{newMArray}

\inferrule
{Ξ ⊢ (Γ||n⇓Δ||i) :_ρ \varid{Int}, (arr:_ρ \varid{MArray}~a, Σ) \\ Ξ ⊢ (Δ||arr⇓Θ||[a_1,…,a_i,…,a_n]) :_ρ
  \varid{MArray}~a, Σ }
{Ξ ⊢ (Γ||\varid{write}~arr~n~a
  ⇓ Γ||[a_1,…,a,…,a_n]) :_ρ \varid{MArray}~a, Σ}\text{write}

\inferrule
{Ξ ⊢ (Γ||arr ⇓ Δ||[a_1,…,a_n]) :_ρ \varid{MArray}~a, Σ}
{Ξ ⊢ (Γ||\varid{freeze}~arr ⇓ Δ,x :_1 \varid{Array a} = [a_1,…,a_n]||\varid{Unrestricted}~x
  ) :_ρ \varid{Unrestricted} (\varid{Array}~a), Σ}\text{freeze}

\inferrule
{Ξ ⊢ (Γ || n ⇓ Δ || i) :_ρ \varid{Int},Σ \\ Ξ ⊢ (Δ||arr ⇓ Θ ||
  [a_1,…,a_i,…,a_n])) :_ρ \varid{Array}~a,Σ \\ Ξ ⊢ (Θ || a_i ⇓ Λ || z)
:_ρ A, Σ}
{Ξ ⊢ (Γ || \varid{read}~arr~n ⇓ Λ || z) :_ρ a, Σ}

%%%% /Arrays
  \end{mathpar}
  \caption{Denotational dynamic semantics}
  \label{fig:typed-semop}
\end{figure}

The ordinary semantics, if a good model of what we are implementing in
practice, is not very convenient to reason about directly. First
mutation is a complication in itself, but it is also difficult to
recover types (or even multiplicity annotations) from a particular
evaluation state.

We address this difficulty by introducing a denotational semantics where the states
are annotated with types and linearity. The denotational semantics
also does not perform mutations: arrays are seen as ordinary values
which we modify by copy.

\begin{definition}[Annotated state]

  An annotated state is a tuple $Ξ ⊢ (Γ||t :_ρ A),Σ$ where
  \begin{itemize}
  \item $Ξ$ is a typing context
  \item $Γ$ is a \emph{typed environment}, \ie a collection of
    bindings of the form $x :_ρ A = e$
  \item $t$ is a term
  \item $ρ∈\{1,ω\}$ is a multiplicity
  \item $A$ is a type
  \item $Σ$ is a typed stack, \ie a list of triple $e:_ρ A$ of
    a term, a multiplicity and an annotation.
  \end{itemize}

  Terms are extended with array expressions: $[a_1, …, a_n]$ where the
  $a_i$ are variables.

\end{definition}

Let us introduce a notation which will be needed in the definition of
well-typed state.
\begin{definition}[Weighted pairs]
  We define a type of left-weighted pairs:

  $$\data a~{}_π\!⊗ a = ({}_π\!,) : a →_π b ⊸ a~{}_π\!⊗ b$$

  Let us remark that
  \begin{itemize}
  \item We have not introduced type parameters in data types, but it
    is straightforward to do so
  \item We annotate the data constructor with the multiplicity $π$,
    which is not mandated by the syntax. It will make things simpler.
  \end{itemize}

\end{definition}

Weighted pairs are used to internalise a notion of stack that keeps
track of multiplicities in the following definition, which defines
when annotated states are well-typed.

\begin{definition}[Well-typed state]
  We say that an annotated state is well-typed if the following
  typing judgement holds:
  $$
  Ξ ⊢ \flet Γ \fin (t,\termsOf{Σ}) : (A~{}_ρ\!⊗\multiplicatedTypes{Σ})‌
  $$
  Where $\flet Γ \fin e$ stands for the use of $Γ$ as a sequence of
  let-bindings with the appropriate mulitplicity\footnote{We skip over
    the case of mutually recursive bindings in our presentation. But
    we can easily extend the formalism with then. Recursive bindings
    must be of multiplicity $ω$, and mutually recursive definition are
    part of a single $\flet$ block. When defining $\flet Γ$ we need to
    pull a mutually recursive block as a single $\flet$ block as
    well.}, $\termsOf{e_1 :_{ρ_1} A_1, … , e_n :_{ρ_n} A_n}$ for
  $(e_1~{}_{ρ_1}\!, (…, (e_n~{}_{ρ_n},())))$, and
  $\multiplicatedTypes{e_1 :_{ρ_1} A_1, … , e_n :_{ρ_n} A_n}$ for
  $A_1~{}_{ρ_1}\!⊗(…(A_n~{}_{ρ_n}\!⊗()))$.
\end{definition}

\begin{definition}[Denotational reduction relation]
  We define the denotational reduction relation, also written $⇓$, as a
  relation on annotated states. Because $Ξ$, $ρ$, $A$ and $Σ$ are
  always the same for related states, we abbreviate
  $$
  (Ξ ⊢ Γ||t :_ρ A,Σ) ⇓ (Ξ ⊢ Δ||z :_ρ A,Σ)
  $$
  as
  $$
  Ξ ⊢ (Γ||t ⇓ Δ||z) :_ρ A, Σ
  $$

  The denotational reduction relation is defined inductively by the
  rules of \fref{fig:typed-semop}.

  A few rules of notice:
  \begin{description}
  \item[linear variable] linear variables are removed from the
    environment when they are evaluated: they are no longer accessible
    (if the state is well-typed)
  \item[let] even if we are evaluating a $\flet_1$m we may have to
    introduce a non-linear binding in the environemnt: if the value we
    are currently computing will be used as the argument of a
    non-linear function, the newly introduced variables may be forced
    several times (or not at all). An example is
    $\flet[ω] x = (\flet[1] y = \varid{True}) \fin y \fin (x,x)$: if evaluating
    this example yielded the binding $y :_1 Bool = True$, then the
    intermediate state would be ill-typed. So for the sake of proofs,
    instead we add $y :_ω Bool = True$ to the environment
  \item[write] No mutation is performed in array write: we just return
    a new copy of the array.
  \end{description}

\end{definition}

The denotation semantics preserves the well-typedness of annotated
states throughout the evaluation\fref{lem:type-safety}. From then on, we
will only consider the evaluation of well-typed states.

\begin{lemma}[Denotational evaluation preserves typing]\label{lem:type-safety}
  If  $Ξ ⊢ (Γ||t ⇓ Δ||z) :_ρ A, Σ$, or $Ξ ⊢ (Γ||t ⇓^* Δ||z) :_ρ A, Σ$ then
  $$
  Ξ ⊢ (Γ||t :_ρ A),Σ \text{\quad{}implies\quad{}} Ξ ⊢ (Δ||z :_ρ A),Σ.
  $$
\end{lemma}
\begin{proof}
  By induction on the typed-reduction.
\end{proof}

\subsection{Bisimilarity and all that}

The crux of our meta-theory is that the two semantics are
bisimilar. Bisimilarity allows to tranport properties from the
denational semantics, on which it is easy to reason, and the ordinary
semantics which is close to the implementation. It also makes it
possible to prove observational equality results. Our first definition
is the relation between the states of the ordinary evaluation and
those of the denotational evaluation which witnesses the bisimulation.

\begin{definition}[Denotation assignment]
  A well-typed state is said to be a denotation assignment for an ordinary
  state, written $\ta{Γ:e}{Ξ ⊢ Γ' || e' :_ρ A , Σ}$, if
  $e[Γ_1]=e' ∧ Γ' = Γ''[Γ_1] ∧ Γ'' \leqslant Γ_ω$. Where
  \begin{itemize}
  \item $Γ_ω$ is the restriction of $Γ$ (a context of the ordinary
    semantics) to the variable bindings $x :_ω A = u$
  \item $Γ_1$ is the restriction of $Γ$ to the array bindings $l :_1 A
    = [a_1, …, a_n]$, seen as a substitution.
  \end{itemize}
  That is, $Γ'$ is allowed to strengthen some $ω$ bindings to be
  linear, and to drop unnecessary bindings. Array pointers are
  substituted with their value (since we have array pointers in the
  ordinary semantics but only array values in the denotational
  semantics). The substitution is subject to

  The substitution must abide by the following restrictions in order
  to preserve the invariant that |MArray| pointers are not shared:
  \begin{itemize}
  \item An |MArray| pointer in $Γ_1$ is substituted either exactly
    in one place in $Γ''$ or exactly in one place in $e$.
  \item If an |MArray| pointer is substituted in $Γ''$ then it is
    substituded in a linear binding $x :_1 A = u$
  \item If an |MArray| pointer is substituted in $e$ the $ρ=1$
  \item If an |MArray| pointer is substituted in the body $u$ as of
    $let_p x = u in v$ (sub)expression, the $p=1$
  \end{itemize}
\end{definition}

\begin{lemma}[Safety]\label{lem:actual_type_safety}
  The denotation assignment relation defines a simulation of the
  ordinary evaluation by the denotational evaluation, both in the
  complete and partial case.

  That is:
  \begin{itemize}
  \item for all $\ta{Γ:e}{Ξ ⊢ (Γ'||e) :_ρ A,Σ}$ such that $Γ:e⇓Δ:z$,
    there exists a well-typed state $Ξ ⊢ (Δ'||z) :_ρ A,Σ$ such that
    $Ξ ⊢ (Γ||t ⇓ Δ||z) :_ρ A, Σ$ and $\ta{Δ:z}{Ξ ⊢ (Δ'||z) :_ρ A,Σ}$.
  \item for all $\ta{Γ:e}{Ξ ⊢ (Γ'||e) :_ρ A,Σ}$ such that $Γ:e⇓^*Δ:z$,
    there exists a well-typed state $Ξ ⊢ (Δ'||z) :_ρ A,Σ$ such that
    $Ξ ⊢ (Γ||t ⇓^* Δ||z) :_ρ A, Σ$ and $\ta{Δ:z}{Ξ ⊢ (Δ'||z) :_ρ A,Σ}$.
  \end{itemize}
\end{lemma}
\begin{proof}
  Both simulations are proved by a similar induction on the derivation
  of $Γ:e⇓Δ:z$ (resp. $Γ:e⇓Δ:z$):
  \begin{itemize}
  \item The properties of the substitution of |MArray| in the
    definition of denotation assignments are crafted to make the
    \emph{variable} and \emph{let} rules carry through
  \item The other rules are straightforward
  \end{itemize}
\end{proof}

\begin{lemma}[Liveness]\label{lem:liveness}
  The refinement relation defines a simulation of the strengthened
  reduction by the ordinary reduction, both in the complete and
  partial case.

  That is:
  \begin{itemize}
  \item for all $\ta{Γ:e}{Ξ ⊢ (Γ'||e) :_ρ A,Σ}$ such that
    $Ξ ⊢ (Γ'||e ⇓ Δ'||z) :_ρ A,Σ$, there exists a state $Δ:z$ such
    that $Γ:e⇓Δ:z$ and $\ta{Δ:z}{Ξ ⊢ (Δ'||z) :_ρ A,Σ}$.
  \item for all $\ta{Γ:e}{Ξ ⊢ (Γ'||e) :_ρ A,Σ}$ such that
    $Ξ ⊢ (Γ'||e ⇓^* Δ'||z) :_ρ A,Σ$, there exists a state $Δ:z$ such
    that $Γ:e⇓^*Δ:z$ and $\ta{Δ:z}{Ξ ⊢ (Δ'||z) :_ρ A,Σ}$.
  \end{itemize}
\end{lemma}
\begin{proof}
  Both are proved by a straightforward induction over the derivation of
  $Ξ ⊢ (Γ'||e ⇓ Δ'||z) :_ρ A,Σ$ (resp. $Ξ ⊢ (Γ'||e ⇓ Δ'||z) :_ρ A,Σ$).
\end{proof}

Equipped with this bisimulation, we are ready to prove the theorems of
\fref{sec:metatheory}.

{
\renewcommand{\thetheorem}{\ref{thm:progress}}
\begin{theorem}[Progress]
  Evaluation does not block. That is, for any partial derivation of
  $Ξ ⊢ (Γ'||e ⇓ ?) :_ρ A,Σ$ or of $Γ:e⇓?$, the derivation can be
  extended.

  In particular, typestates need not be checked dynamically.
\end{theorem}
\addtocounter{theorem}{-1}
}
\begin{proof}
  By liveness (\fref{lem:liveness}) it is sufficient to prove the case
  of the denotational semantics.

  Let us also note that if we erase all multiplicity from the
  denotational semantics, then we get a completely standard semantics
  for simply typed $λ$-calculus, in which progress is known to
  hold. So we it suffices to show that multiplicity annotations do not prevent the
  head of the partial derivation to match a rule.

  In other word, we must prove that a state of the form
  $Ξ⊢Γ,x:_1 B = e||x :_ω A,Σ$ is not reachable. Notice that
  $Ξ⊢Γ,x:_1 B = e||x :_ω A,Σ$ is not a well-typed state because it
  reduces to $x:_1B = x:_{ωπ} B$ for some $π$, which never holds. By
  type preservation (\fref{lem:type-safety}),
  $Ξ⊢Γ,x:_1 B = e||x :_ω A,Σ$ cannot be the head of a partial
  derivation.
\end{proof}

Observational equivalence, which means, for \calc{}, that an
implementation in terms of in-place mutation is indistinguishable from
a pure implementation, is phrased in terms of the |Bool|: any
distinction which we can make between two evaulations can be
extended so that one evaluates to |False| and the other to |True|.
{
\renewcommand{\thetheorem}{\ref{thm:obs-equiv}}
\begin{theorem}[Observational equivalence]
  The ordinary semantics, with in-place mutation is observationally equivalent
  to the pure denotational semantics.

  That is, for all $\ta{⋅:e}{⊢ (⋅||e) :_ρ \varid{Bool},⋅}$, if $⋅:e ⇓ Δ:z$ and
  $⋅ ⊢ (⋅||e⇓ Δ||z')  :_ρ \varid{Bool}, ⋅ $, then $z=z'$
\end{theorem}
\addtocounter{theorem}{-1}
}
\begin{proof}
  Because the semantics are deterministic, this is a direct
  consequence of bisimilarity.
\end{proof}


\end{document}

% safety proves that the mutable semantics is equivalent to a pure
% semantics.
% liveness proves that the primitives don't block on typestate (\eg in the
% write primitive, we are never given an |Array|) (because typing is
% preserved in the denotational semantics, hence the denotational
% semantics can't block on a typestate).

% Local Variables:
% ispell-local-dictionary: "british"
% End:

%  LocalWords:  FHPC Lippmeier al honda pq th ffi monadic runLowLevel
%  LocalWords:  forkIO initialContext runtime doneWithContext Primops
%  LocalWords:  deallocation Launchbury launchbury gc scrutinee dup
%  LocalWords:  centric polymorphism modality intuitionistic typable
%  LocalWords:  compositional Andreoli's openfile myfile ReadMore ys
%  LocalWords:  hClose xs deallocated linearities mcbride snd inlined
%  LocalWords:  unboxed Haskellian api newByteArray MutableByteArray
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
%  LocalWords:  unannotated tuple subkinding invertible coeffects ghc
%  LocalWords:  unrestrictedly bidirectionality GADT reify finaliser
%  LocalWords:  Finalisers effectful subtyping parameterised Inlining
%  LocalWords:  inlining cardinality forM mapM pessimisation APIs RTS
%  LocalWords:  SpriteKit chakravarty spritekit IORef ImperativeNode
%  LocalWords:  invariants
