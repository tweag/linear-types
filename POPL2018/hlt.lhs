% -*- latex -*-

%% For double-blind review submission
% \documentclass[acmsmall,10pt,review,anonymous]{acmart}\settopmatter{printfolios=true}
%% For single-blind review submission
% \documentclass[acmsmall,10pt,review]{acmart}\settopmatter{printfolios=true}
%% For final camera-ready submission
\documentclass[acmsmall,10pt]{acmart}\settopmatter{}

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
\def\frefsecname{Section}
\def\freffigname{Figure}
\def\frefdefname{Definition}
\def\Frefdefname{Definition}
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
\newcommandx{\critical}[2][1=]{\todo[linecolor=blue,backgroundcolor=blue!25,bordercolor=red,#1]{#2}}
\newcommandx{\improvement}[2][1=]{\todo[linecolor=pink,backgroundcolor=pink!25,bordercolor=pink,#1]{#2}}
\newcommandx{\resolved}[2][1=]{\todo[linecolor=OliveGreen,backgroundcolor=OliveGreen!25,bordercolor=OliveGreen,#1]{#2}} % use this to mark a resolved question
\newcommandx{\thiswillnotshow}[2][1=]{\todo[disable,#1]{#2}} % will replace \resolved in the final document

% Peanut gallery comments by Ryan:
\newcommandx{\rn}[1]{\todo[]{RRN: #1}}
\newcommandx{\simon}[1]{\todo[]{SPJ: #1}}
\newcommandx{\jp}[1]{\todo[linecolor=blue,bordercolor=blue,backgroundcolor=cyan!10]{#1}{}}
\newenvironment{alt}{\color{red}}{}

% Link in bibliography interpreted as hyperlinks.
\newcommand{\HREF}[2]{\href{#1}{#2}}

% \newtheorem{definition}{Definition}
% \newtheorem{lemma}{Lemma}
\newtheorem{remark}{Remark}

\newcommand\HaskeLL{Hask-LL}
\newcommand\calc{{\ensuremath{λ^q_\to}}}


%%%%%%%%%%%%%%%%% Author's configuration %%%%%%%%%%%%%%%%%

%% Some recommended packages.
\usepackage{booktabs}   %% For formal tables:
                        %% http://ctan.org/pkg/booktabs
\usepackage{subcaption} %% For complex figures with subfigures/subcaptions
                        %% http://ctan.org/pkg/subcaption


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
  path forward to integrate with existing languages such as Ocaml or
  Haskell. In this paper, we introduce and study a linear type system
  designed with two crucial properties in mind:
  backwards-compatibility and code reuse across linear and non-linear
  users of a library. Only then can the benefits of linear types
  permeate conventional functional programming.  Rather than bifurcate
  % not just data; functions must also be bifurcated due to closures.
  types into linear and non-linear counterparts, we instead
  attach linearity to {\em binders}.  Linear function types can
  receive inputs from linearly-bound values, but can also operate over
  unrestricted, regular values.

  To demonstrate the efficacy of our linear type system~---~both how
  easy it can be integrated in an existing language implementation and
  how streamlined it makes it to write program with linear
  types~---~we implemented our type system in a branch of
  \textsc{ghc}, the leading Haskell compiler, and demonstrate, with
  it, two kinds of applications of linear types: making functions,
  that otherwise would be considered to have side effects, pure; and
  enforcing protocols in \textsc{i/o}-performing functions.
\end{abstract}


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
\keywords{Haskell, laziness, linear logic, Linear types, systems
  programming}  %% \keywords is optional


%% \maketitle
%% Note: \maketitle command must come after title commands, author
%% commands, abstract environment, Computing Classification System
%% environment and commands, and keywords command.
\maketitle


\section{Introduction}

Despite their obvious promise, and a huge research literature, linear
type systems have not made it into mainstream programming languages,
even though linearity has inspired uniqueness typing in Clean, and
ownership typing in Rust.  We take up this challenge by extending
Haskell with linear types.

\jp{What about ``Even though our design supports many
  applications for linear types, we demonstrate that our design
  supports two typical use-cases.''}  Linear types can do many
things, but we focus on two particular use-cases.  First, safe
update-in-place for mutable structures, such as arrays; and second,
enforcing access protocols for external APIs, such as files, sockets,
channels and other resources.  Our particular contributions are these
\begin{itemize}
\item Our extension to Haskell, dubbed \HaskeLL, is
      \emph{non-invasive}.  Existing programs continue to typecheck,
      and existing data types can be used as-is even in linear parts
      of the program.
\item The key to this non-invasiveness is that, in contrast most other
      approaches, we focus on \emph{linarity on the function arrow}
      rather than \emph{linearity on the types} (\fref{sec:lin-arrow}).
    \item Linearity on the function arrow alone is not enough: a
      linear function must be able to return both linear and
      non-linear results.  \jp{I am not sure what this means nor how
        it connects with the next sentence.  Do you intend the following? ``Linear
        functions are not sufficient on their own. Data types must
        also be adjusted, so that they can be used to store linear and
        unrestricted values.'' } We make a simple extension to
      algebraic data type declarations to support this need
      (\fref{sec:datattypes}).
\item A benefit of linearity-on-the-arrow is that it naturally supports
      \emph{linearity polymorphism} (\fref{sec:lin-poly}).  This contributes
      to a smooth extension of Haskell by allowing many existing functions
      (map, compose, etc) to be given more general types, so they can
      work uniformly in both linear and non-linear code.
\item We formalise our system in a small, statically-typed core
      calculus that exhibits all these features (\fref{sec:calculus}).
      It enjoys the usual properties of progress and preservation.
\item We have implemented a prototype of system in as a modest extension to \textsc{ghc}
      (\fref{sec:impl}), which substantiates our claim of non-invasiveness.
      Our prototype type performs linearity \emph{inference}, but a systematic
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
are aliases to the value; update-in-place is OK if there are no other pointers to it.
Linearity supports a more efficient implementation, by O(1) update rather than O(n) copying. \jp{This is really a special case of the next item}
\item \emph{Am I obeying the usage protocol of this external resource}
(\fref{sec:io-protocols})?
For example, an open file should be closed, and should not be used after it it has been closed;
a socket should be opened, then bound, and only then used for reading; a malloc'd memory
block should be freed, and should not be used after that.
Here, linearity does not affect efficiency, but rather eliminates many bugs.
\end{itemize}
We introduce our extension to Haskell, which we call \HaskeLL, by focusing on these
two use-cases.   In doing so, we introduce a number of ideas that we flesh out in
subsequent subsections.


\subsection{Safe mutable arrays}
\label{sec:freezing-arrays}
\begin{figure}
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
\caption{Type signatures for array primitives (currrent \textsc{ghc})}
\label{fig:array-sigs}
\end{figure}

\begin{figure}
\begin{code}
  type MArray a
  type Array a

  newMArray :: Int -> (MArray a ⊸ Unrestricted b) ⊸ b
  write :: MArray a ⊸ (Int, a) -> MArray a
  read :: MArray a ⊸ Int -> (MArray a, Unrestricted a)
  freeze :: MArray a ⊸ Unrestricted (Array a)
\end{code}
\caption{Type signatures for array primitives (linear version)}
\label{fig:linear-array-sigs}
\end{figure}
The Haskell language provides immutable arrays, built with the function |array|\footnote{
Haskell actually generalises over the type of array indices, but for this
paper we will assume that the arrays are indexed, from 0, by |Int| indices.}:
\begin{code}
array :: (Int,Int) -> [(Int,a)] -> Array a
\end{code}
But how is |array| implemented? A possible answer is ``it is built-in; don't ask''.
But in reality \textsc{ghc} implements |array| using more primitive pieces, so that library authors
can readily implement variations (which they certainly do).  Here is the
definition of |array|, using library functions whose types are given
in \fref{fig:array-sigs}:
\begin{code}
array :: Int -> [(Int,a)] -> Array a
array size pairs = runST (do  { ma <- newMArray size
                              ; forM_ pairs (write ma)
                              ; return (unsafeFreeze ma) })
\end{code}
In the first line we allocate a mutable array, of type |MArray s a|.
Then we iterate over the |pairs|, with |forM_|, updating the array in place
for each pair.  Finally, we freeze the mutable array, returning an immutable
array as required.  All this is done in the |ST| monad, using |runST| to
securely encapsulate an imperative algorithm in a purely-functional context,
as described in \cite{launchbury-pj:state-in-haskell}.

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
be done in parallel, but the |ST| monad would serialise them.

Linear types allow a more secure and less sequential interface.
\HaskeLL{} introduces a new kind of function type: the \emph{linear
arrow} |a⊸b|. A linear function |f :: a⊸b| must consume its argument
\emph{exactly once}. This new arrow is used in
a new array \textsc{api}, given in \fref{fig:linear-array-sigs}.  Using
this \textsc{api}  we can define |array| thus:
\begin{code}
array :: Int -> [(Int,a)] -> Array a
array size pairs = newMArray size (\ma -> freeze (foldl write ma pairs))
\end{code}
\simon{I have gneralised the type of |newMArray| so it does not have
to return an unrestricted value.  Is that right?}
There are several things to note here:
\begin{itemize}
\item We still disinguish the type of mutable arrays |MArray| from that of
immutable arrays |Array|.
\item The function |newMArray| allocates a fresh, mutable array of the specified
size, and passes it to the function supplied as the second argument to |newMArray|.
\item That function has the linear type |(MArray a ⊸ Unrestricted b)|; the
lollipop arrow says that the function guarantees to consume the mutable array
exactly once; it will neither discard it nor use it twice.  We will define
``consume'' more precisely in \fref{sec:consume}.
\item Since |ma| is a linear array, we cannot pass it to many calls to
|write|.  Instead, each call to |write| returns a new array, so that the
array is single-threaded, by |foldl|, through the sequence of writes.
\item The call to |freeze| consumes the mutable array and produces an immutable one.
Because it consumes its input, there is no danger of the same mutable array being
subsequently written to, eliminating the problem with |unsafeFreeze|.
\item The result of |freeze| is an immutable array that can be freely shared.
But in our system, \emph{linearity is a property of function arrows,
not of types} (\fref{sec:lin-arrow}), so we need some way to say that the
result of |freeze| can be freely shared.  That is what the |Unrestricted|
type does.  However, |Unrestricted| is just a library type; it does not have to
be built-in (See \fref{sec:data-types}).
\item The function |foldl| has the type
\begin{code}
foldl :: (a ⊸ b ⊸ a) -> a ⊸ [b] ⊸ a
\end{code}
which expresses that it consumes its second argument linearly
(in this case the mutable array), while the function it is given as
its first argument (in this case |write|) must be linear.
As we shall see in \fref{sec:lin-poly} this is not new |foldl|, but
just an instance of a more general, multiplicity-polymorphic version of
a single |foldl|.
\end{itemize}
The |ST| monad has disappeared altogether; it is the array \emph{itself}
that must be single threaded, not the operations of a monad. That removes
the unnecessary sequentialisation that we mentioned earlier.

Compared to the status quo (using |ST| and |unsafeFreeze|), the main gain
is in shrinking the trusted code base, because more library code (and it
can be particularly gnarly code) is statically typechecked.  Clients who
use immutable arrays do not see the inner workings of the library, and will
be unaffected.  Our second use-case has a much more direct impact on library clients.

\subsection{I/O protocols} \label{sec:io-protocols}

% On the other hand, in other cases, we need actions to be fully
% sequentialised, because they are interacting with the real world. This
% is the world of |IO| action. In this case, linearity will not serve to
% make the program less sequentialised~---~it must not be~---~but will
% help make sure that a sequence of actions obey a certain discipline. We
% think of such disciplines as protocols\footnote{Such protocol can be
%   imposed on actual network communications, in which case they are
%   actual communication protocols. See
%   \citet{wadler_propositions_2012,parente_logical_2015}, for a formal
%   treatment of such communication protocols.}.
%
% A common example of such protocol is network- or storage-based
% collection. For example databases: the common feature is that getting
% (or setting) an element of this collection requires I/O, hence, in
% Haskell, happens in the |IO| monad.
\begin{figure}
\begin{code}
  type File a
  openFile :: FilePath -> IOL 1 (File ByteString)
  readLine :: File a ⊸ IOL 1 (File a, Unrestricted a)
  closeFile :: File a ⊸ IOL ω ()
\end{code}
\caption{Types for linear file IO} \label{fig:io-linear}
\end{figure}

Consider this \textsc{api} for files:
\begin{code}
  type File a
  openFile :: FilePath -> IO (File ByteString)
  readLine :: File a -> IO a
  closeFile :: File a -> IO ()
\end{code}
Here we see |File a| as a cursor in a file. Each call
to |readLine| returns an |a| (the line) and moves the cursor one line
forward.  But nothing stops us reading a file after we have closed it,
or forgetting to close it.
An alternative \textsc{api} using linear types is given in \fref{fig:io-linear}.
Using it we can write a simple file-handling program:
\begin{code}
firstLine :: FilePath -> Bytestring
firstLine fp = do  { f <- open fp
                   ; (f, Unrestricted bs) <- readLine f
                   ; close f
                   ; return bs }
\end{code}
Notice several things
\begin{itemize}
\item Operations on files remain monadic, unlike the case with mutable arrays.
I/O operations affect the world, and hence must be sequenced.  It is not enough
to sequence operations on files individually, as it was for arrays.
\item We generalise the IO monad so that it expresses whether or not the
returned value is linear.  We add an extra type parameter |p| to the monad |IOL|,
where |p| can be |1| or |ω|.  Now |openFile| returns |IO 1 (File ByteString)|,
the ``|1|'' indicating that the returned |File| must be used linearly.\footnote{Using |ω| indicates on the contrary that a result can be used in an unrestricted fashion.}
We will return to how |IOL| is defined in \fref{sec:linear-io}.
\item As before, operations on linear values must consume their input
and return a new one; here |readLine| consumes the |File| and produces a new one.
\item Unlike the |File|, the |ByteString| returned by |readLine| is unrestricted,
and the type of |readLine| indicates this.
\end{itemize}
It may seem tiresome to have to thread the |File| as well as sequence
operations with the IO monad. But in fact it is often very useful do
to so, as we will see in \fref{sec:sockets}, because we can use a
phantom type to encode the state of the resource (similar to a
typestate).

% \subsection{Lifting files}
%
% \simon{I doubt we want this material; just leaving it here for now}
%
% We will want that |File| behaves as much as possible as an ordinary
% collection. In particular we would like to |File| to be a functor:
% this is how we will parse lines.
% \begin{code}
%   mapFile :: (a->b) -> File a -> File b
% \end{code}
% We may also want ways to compose |File|s. For instance a way to zip to
% files:
% \begin{code}
%   zipFile :: File a -> File b -> File (a,b)
% \end{code}
% Such a programing idiom can be found in the
% \texttt{streaming}~\cite{thompson_streaming_2015} library.
%
% The problem is that it makes a number of unintended things
% possible. We have observed such mistakes in our own code in industrial
% projects, and it proved quite costly to hunt down.
% \begin{code}
%   bad1 path = do
%     file <- openFile path
%     let coll = map someParsingFun file
%     string <- readLine file
%     value <- readLine coll
%     closeFile coll
%
%   bad2 path = do
%     file <- openFile path
%     let coll = map someParsingFun file
%     closeFile file
%     value <- readLine coll
%     closeFile coll
%
%   bad3 path1 path2 = do
%     file1 <- openFile path
%     file2 <- openFile path
%     coll <- zipFile file1 file2
%     string <- readLine file1
%     value <- readLine coll
%     closeFile coll
%
%   bad4 path1 path2 = do
%     file1 <- openFile path
%     file2 <- openFile path
%     coll <- zipFile file1 file2
%     closeFile file1
%     closeFile coll
%
% \end{code}
% In |bad1|, the process reads from both handlers to the same file,
% reads from |file| will cause the cursor in |line| to progress. The
% matter gets worse in |bad3| where the |file1| and |file2| are supposed
% to be read in lockstep, but they get desynchronised by the call to
% |readLine file1|. In |bad2|, |file1| is closed before |coll| is read,
% and in |bad4|, |file1| is closed twice, once directly, and a second
% time via |closeFile coll|.
%
% The issue is that the intention behind |mapFile| and |zipFile| is that
% the handle is transformed, not shared. It is a crucial difference with
% immutable collections which can be shared freely.
%
% The following \textsc{api} for |File| makes all the examples above
% ill-typed, ensuring that we don't use the same handle under two
% different guises at the same time. It ensures, in particular, that
% every file is closed exactly once.
% \begin{code}
%   type File a
%
%   openFile :: FilePath -> IO 1 (File ByteString)
%   readLine :: File a ⊸ IO 1 (Unrestricted a, File a)
%   closeFile :: File a -> IO ω ()
%   mapFile :: (a->b) -> File a ⊸ File b
%   zipFile :: File a ⊸ File b ⊸ File (a,b)
% \end{code}
%
% There is a price to pay in that we have to thread files at every use,
% even for |readLine|. Note, however, that the \texttt{streaming}
% library's \textsc{api} shares this characteristic, despite not using
% linear types. What we gain for this price is a guarantee that files
% will be closed exactly once and that we are not using two versions of
% a file.\unsure{If we talk about borrowing, we can even alleviate that
%   cost by having |readLine :: File a -> _ β IO ω a|.}
%
% Sometimes, however, you may want to have two versions of the same
% file. There are two possible semantics: any-cast~---~the two versions of
% the file read from the same cursor, and each line is read by only
% one of the two versions~---~and multi-cast where lines are read by
% both versions. Thanks to linear types you must specify when you want
% to versions of a file, at which point you can choose between any-cast
% and multi-cast.
% \begin{code}
%   dupFileAny    :: File a ⊸ (File a, File a)
%   dupFileMulti  :: File a ⊸ (File a, File a)
% \end{code}
%
% We have wilfully ignored, so far, the fact that files are finite, and
% that |readLine| may reach the end of the file. The real type of
% |readLine| should be:
% \begin{code}
%   readLine :: File a ⊸ IO 1 (Maybe (Unrestricted a, File a))
% \end{code}
% Which is like pattern matching a list, except in |IO|. Note that if
% we reach the end of the file, no new |File a| is returned, which means
% that |readLine| will close the file handle in that case. So
% |closeFile| only needs to be called when we do not want to consume the
% entire file.

\subsection{Operational intuitions}
\label{sec:consume}

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
\item To consume exactly once a value of an atomic base type, like |Int| or |Ptr|, just evaluate it.
\item To consume a function exactly once, call it, and consume its result exactly once.
\item To consume a pair exactly once, evaluate it and consume each of its components exactly once.
\item More generally, to consume exactly once a value of an algebraic data type, evaluate
  it and consume all its linear components exactly once (\fref{sec:non-linear-constructors}).
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

\subsection{Linear data types}
\label{sec:linear-constructors}
\label{sec:datattypes}

With the above intutions in mind, what type should we assign to a data
constructor such as the pairing constructor |(,)|?  Here are two possibilities:
\begin{code}
 (,) ::  a ⊸ b ⊸ (a,b)
 (,) ::  a -> b -> (a,b)
\end{code}
Using the definition in \fref{sec:consumed}, the former is clearly the right
choice: if the result of |(,) e1 e2| is consumed exactly once,
then (by \fref{def:consume}),
|e1| and |e2| are each consumed exactly once; and hence |(,)| is linear it its
arguments.

So much for construction; what about pattern matching?  Consider:
\begin{code}
f1 :: (Int,Int) -> (Int,Int)
f1 x = case x of (a,b) -> (a+a,0)

f2 :: (Int,Int) ⊸ (Int,Int)
f2 x = case x of (a,b) -> (b,a)
\end{code}
|f1| is an ordinary Haskell function. Even though the data constructor |(,)| has
a linear type, that does \emph{not} imply that the pattern-bound variables must be
consumed exactly once.

However |f1| does not have the linear type |(Int,Int) ⊸ (Int,Int)|.
Why not?  If the result of |(f1 t)| is consumed once, is |t| guaranteed to be consumed
once?  No: |t| is guaranteed to be evaluated once, but its first component is then
consumed twice and its second component not at all.
In contrast, |f2| \emph{does} have a linear type: if |(f2 t)| is consumed exactly once,
then indeed |t| is consumed exactly once.

The key point here is that \emph{the same pair constructor works in both functions;
we do not need a special non-linear pair}.

The same idea applies to all existing Haskell data types: we (re)-define
their constuctors to use a linear arrow.  For example here is a declaration
of \HaskeLL{}'s list type:
\begin{code}
data [a] where
  []   :: [a]
  (:)  :: a ⊸ [a] ⊸ [a]
\end{code}
Just as with pairs, this is not a new, linear list type: this \emph{is}
\HaskeLL{}'s list type, and all existing Haskell functions will work
over it perfectly well.
Even better, many list-based functions are in fact linear, and
can be given a more precise type. For example we can write |(++)| as
follows:
\begin{code}
(++) :: [a] ⊸ [a] ⊸ [a]
[]      ++ ys = ys
(x:xs)  ++ ys = x : (xs ++ ys)
\end{code}
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
type to contain linear values (such as mutable arrays) without
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
constructor |PLU|, with mixed linearity.
Now, when \emph{constructing} a |PLU| pair the type of the constructor means
that we must always supply an unrestricted second argument; and dually
when \emph{pattern-matchinng} on |PLU| we are therefore free use the second argument
in an unrestricted way, even if the |PLU| value itself is linear.

Instead of defining a pair with mixed linearity, we can also write
\begin{code}
  data Unrestricted a where { Unrestricted :: a → Unrestricted a }

  f :: (MArray Int, Unrestricted Int) ⊸  MArray Int
\end{code}
The type |(Unrestricted t)| is very like |!t| in linear logic, but to us
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

\subsection{Linearity polymorphism}
\label{sec:lin-poly}

A linear function provides more guarantees to its caller than
a non-linear one -- it is more general.  But the higher-order
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
Likewise, function composition can be given the following general type:
\begin{code}
(∘) :: forall p q. (b → _ p c) ⊸ (a → _ q b) → _ p a → _ (p q) c
(f ∘ g) x = f (g x)
\end{code}
That is: two functions that accept arguments of arbitrary
multiplicities (|p| and |q| respectively) can be composed to form a
function accepting arguments of multiplicity |pq| (\emph{i.e.} the
product of |p| and |q| --- see \fref{def:equiv-multiplicity}).
%
Finally, from a backwards-compatibility perspective, all of these
subscripts and binders for multiplicity polymorphism can be
ignored. Indeed, in a context where client code does not use
linearity, all inputs will have multiplicity $ω$, and transitively all
expressions can be promoted to $ω$. Thus in such a context the
compiler, or indeed documentation tools, can even altogether hide
linearity annotations from the programmer when this language
extension is not turned on.

\subsection{Linear input/output} \label{sec:linear-io}

In \fref{sec:io-protocols} we introduced the |IOL|
monad.\footnote{|IOL p| is not a monad in the strict sense, because
  |join :: IOL p (IOL q a) ⊸ IOL (pq) a| and we do not have the law
  |pp = p|. We believe that it is a relative
  monad~\cite{altenkirch_monads_2010}.}  But how does it work?  |IOL|
is just a generalisation of the |IO| monad, thus:
\begin{code}
  type IOL p a
  returnIOL :: a -> _ p IOL p a
  bindIOL   :: IO p a ⊸ (a -> _ p IOL q b) ⊸ IOL q b
\end{code}
The idea is that if |m :: IO 1 t|, then |m| is a input/output
computation that returns a linear value of type |t|.  But what does it mean to
``return a linear value'' in a world where linearity applies only to
function arrows?  Fortunately, in the world of monads each computation
has an explicit continuation, so we just need to control the linearity of
the continuation arrow.  More precisely, in an application |m `bindIOL` k|
where |m :: IO 1 t|, we need the continuation |k| to be linear, |k :: t ⊸ IO q t'|.
And that is captured by the linearity-polymorphic type of |bindIOL|.

Even though they have a different type than usual, the bind and return
combinators of |IOL| can be used in the familiar way. The difference
with the usual monad is that multiplicities may be mixed, but this
poses no problem in practice.  Consider
\begin{code}
  do  { f <- openFile s   -- |openFile :: FilePath -> IO 1 (File ByteString)|
      ; d <- getData      -- |getDate  :: IO ω Date|
      ; e[f,d] }
\end{code}
Here |openFile| returns a linear |File| that should be closed, but |getDate| returns
an ordinary non-linear |Date|.  So this sequence of operations has mixed linearity.
Nevertheless, the we can combine them with |bindIOL| in the usual way:
\begin{code}
  openFile s `bindIOL` \f ->
  getData    `bindIOL` \d ->
  e[f,d]
\end{code}
Such an interpretation of the |do|-notation requires the
\texttt{-XRebindableSyntax} extension, but if linear I/O becomes
commonplace it would be worth considering a more robust solution.

Internally, hidden from clients, \textsc{ghc} actually implements |IO| as a function,
and that implementation too is illuminated by linearity, like so:
\begin{code}
data World
newtype IOL p a = IOL (unIOL :: World ⊸ IORes p a)
data IORes p a where
  IOR :: World ⊸ a -> _ p IOR p a

bindIOL   :: IO p a ⊸ (a -> _ p IOL q b) ⊸ IOL q b
bindIOL (IOL m) k = IOL (\w -> case m w of
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
given the type of |(,)| in \fref{sec:linear-constructors}. If |(f x)|
is consumed exactly once, then each component of its result pair is
consumed exactly once, and hence |x| is consumed exactly once.
But |f| is certainly not strict: |f undefined| is not |undefined|.

\section{\calc{}: a core calculus for \HaskeLL}
\label{sec:statics}
\label{sec:calculus}

It would be impractical to formalise all of \HaskeLL{}, so instead we
formalise a core calculus, \calc{}, which exhibits all the key features
of \HaskeLL{}, including data types and linearity polymorphism.  In this
way we make precise much of the informal discussion above.

\subsection{Syntax}
\label{sec:syntax}

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
    \data D~π_1~…~π_n~\mathsf{where} \left(c_k : A₁ →_{q₁} ⋯    A_{n_k} →_{q_{n_k}} D\right)^m_{k=1}
  \end{align*}

  \figuresection{Types}
  \begin{align*}
  A,B &::=\\
      & ||  A →_q B &\text{function type}\\
      & ||  ∀ρ. A &\text{multiplicity-dependent type}\\
      & ||  D~π_1~…~π_n &\text{data type}
  \end{align*}

  \figuresection{Terms}
  \begin{align*}
    e,s,t,u & ::= \\
            & ||  x & \text{variable} \\
            & ||  λ_q (x{:}A). t & \text{abstraction} \\
            & ||  t s & \text{application} \\
            & ||  λπ. t & \text{multiplicity abstraction} \\
            & ||  t p & \text{multiplicity application} \\
            & ||  c t₁ … t_n & \text{data construction} \\
            & ||  \case[p] t {c_k  x₁ … x_{n_k} → u_k}  & \text{case} \\
            & ||  \flet[q] x_1 : A₁ = t₁ … x_n : A_n = t_n \fin u & \text{let}
  \end{align*}

  \caption{Syntax of the linear calculus}
  \label{fig:syntax}
  \label{fig:contexts}
\end{figure}

The term syntax of \calc{} is that of a type-annotated (\textit{à la}
Church) simply-typed $λ$-calculus with let-definitions
(\fref{fig:syntax}).  It includes linearity polymorphism, but to avoid clutter
we omit ordinary type polymorphism.
\simon{Save space by putting the syntax of types and context on one line each.}

\calc{} is an explicitly-typed language: each binder is annotated with
its type and multiplicity; and multiplicity abstraction and application
are explicit.  \HaskeLL{} will use type inference to fill in
much of this information, but we do not address the challenges of type
inference here.
\improvement{Though there are some thoughts in \fref{sec:implementation}}

The types of \calc{} (see \fref{fig:syntax}) are simple types with
arrows (albeit multiplicity-annotated ones), data types, and
multiplicity polymorphism.
% The annotated function type is a
% generalisation of the intuitionistic arrow and the linear arrow.
We use the following abbreviations:
\(A → B ≝  A →_ω B\) and
\(A ⊸ B ≝ A →_1 B\).

Data type declarations (see \fref{fig:syntax}) are of the following form:
\begin{align*}
  \data D~π_1~…~π_n~\mathsf{where} \left(c_k : A₁ →_{q₁} ⋯    A_{n_k} →_{q_{n_k}} D\right)^m_{k=1}
\end{align*}
The above declaration means that \(D\) is parameterized over \(n\) multiplicities $π_i$ and has \(m\) constructors \(c_k\),
each with \(n_k\) arguments. Arguments of
constructors have a multiplicity, just like arguments of functions: an
argument of multiplicity $ω$ means that consuming the data constructor once
makes no claim on how often that argument is consumed (\fref{def:consume}).
% the data type can store, at
% that position, data which \emph{must} reside in the dynamic heap;
% while a multiplicity of $1$ means that data at that position
% \emph{can} reside in either heap.
All the variables in the multiplicities $q_i$ must be among
$π_1…π_n$; we write $q[p_1…p_n]$ for the substitution of $π_i$ by
$p_i$ in $q$.

% For most purposes, $c_k$ behaves like a constant with the type
% $A₁ →_{q₁} ⋯ A_{n_k} →_{q_{n_k}} D$. As the typing rules of
% \fref{fig:typing} make clear, this means in particular that from a
% value $d$ of type to save clutter $D$ with multiplicity $ω$, pattern matching
% extracts the elements of $d$ with multiplicity $ω$. Conversely, if all
% the arguments of $c_k$ have multiplicity $ω$, $c_k$ constructs $D$
% with multiplicity $ω$.
%
% Note that, as discussed in \fref{sec:linear-constructors},
% constructors with arguments of multiplicity $1$ are not more general
% than constructors with arguments of multiplicity $ω$, because if, when
% constructing $c u$ with the argument of $c$ of multiplicity $1$, $u$
% \emph{may} be either of multiplicity $1$ or of multiplicity $ω$;
% dually when pattern-matching on $c x$, $x$ \emph{must} be of
% multiplicity $1$ (if the argument of $c$ had been of multiplicity $ω$,
% on the other hand, then $x$ could be used either as having
% multiplicity $ω$ or $1$).

% -------------------------------------------------
\subsection{Static semantics}
\label{sec:typing-contexts}

%%% typing rule macros %%%
\newcommand{\apprule}{\inferrule{Γ ⊢ t :  A →_q B  \\   Δ ⊢ u : A}{Γ+qΔ ⊢ t u  :  B}\text{app}}
\newcommand{\varrule}{\inferrule{ }{ωΓ + x :_1 A ⊢ x : A}\text{var}}
\newcommand{\caserule}{\inferrule{Γ   ⊢  t  : D~p_1~…~p_n \\ Δ, x₁:_{pq_i[p_1…p_n]} A_i, …,
      x_{n_k}:_{pq_{n_k}[p_1…p_n]} A_{n_k} ⊢ u_k : C \\
      \text{for each $c_k : A_1 →_{q_1} … →_{q_{n_k-1}} A_{n_k} →_{q_{n_k}} D~π_1~…~π_n$}}
    {pΓ+Δ ⊢ \case[p] t {c_k  x₁ … x_{n_k} → u_k} : C}\text{case}}
%%% /macros %%%

\begin{figure}
  \begin{mathpar}
    \varrule

    \inferrule{Γ, x :_{q} A  ⊢   t : B}
    {Γ ⊢ λ_q (x{:}A). t  :  A  →_q  B}\text{abs}

    \apprule

    \inferrule{Δ_i ⊢ t_i : A_i \\ \text {$c_k : A_1 →_{q_1} … →_{q_{n-1}}
        A_n →_{q_n} D~π_1~…~π_n$ constructor}}
    {ωΓ+\sum_i q_i[p₁…p_n]Δ_i ⊢ c_k  t₁ … t_n : D~p₁~…~p_n}\text{con}

    \caserule

    \inferrule{Γ_i   ⊢  t_i  : A_i  \\ Δ, x₁:_{q} A₁ …  x_n:_{q} A_n ⊢ u : C }
    { Δ+q\sum_i Γ_i ⊢ \flet[q] x_1 : A_1 = t₁  …  x_n : A_n = t_n  \fin u : C}\text{let}

    \inferrule{Γ ⊢  t : A \\ \text {$π$ fresh for $Γ$}}
    {Γ ⊢ λπ. t : ∀π. A}\text{m.abs}

    \inferrule{Γ ⊢ t :  ∀π. A}
    {Γ ⊢ t p  :  A[p/π]}\text{m.app}
  \end{mathpar}

  \caption{Typing rules}
  \label{fig:typing}
\end{figure}

The static semantics of \calc{} is given in \fref{fig:typing}.  Each
binding in $Γ$, of form \(x :_q A\), includes a multiplicity $q$
(\fref{fig:syntax}).  The familiar judgement \(Γ ⊢ t : A\) should
be read as follows
\begin{quote}
 \(Γ ⊢ t : A\) asserts that consuming the term $t : A$ exactly once will
  consume each binding $(x :_{q} A)$ in $Γ$ with its multiplicity $q$.
\end{quote}
One may want to think of the \emph{types} in $Γ$ as
inputs of the judgement, and the \emph{multiplicities} as outputs.

For example\jp{example of what?}, the rule (abs) for lambda abstraction adds $(x :_{q} A)$ to the
environment $Γ$ before checking the body |t| of the abstraction.
Notice that in \calc{}, the lambda abstraction  $λ_q(x{:}A). t$
is explicitly annotated with multiplicity $q$.  Remember, this
is an explicitly-typed intermediate language; in \HaskeLL{}
this multiplicity is inferred.

The dual application rule (app) is more interesting:
$$\apprule$$
To consume |(t u)| once, we consume |t| once, yielding the
multiplicities in $Γ$, and |u| once, yielding the multiplicies in
$\Delta$.  But if the multiplicity $q$ on |u|'s function arrow is $ω$,
then the function consumes its argument not once but $ω$ times, so all
|u|'s free variables must also be used with multiplicity $ω$. We
express this by multiplying all the multiplicities in $\Delta$ by $q$,
thus $q\Delta$.  Finally we need to add together all the
multiplicities in $Γ$ and $q\Delta$; hence the context $Γ+qΔ$ in the
conclusion of the rule.

In writing this rule we needed to ``scale'' a context by
a multiplicity, and ``add'' two contexts.  We pause to define these operations.
\begin{definition}[Context addition]~
  \begin{align*}
    (x :_p A,Γ) + (x :_q A,Δ) &= x :_{p+q} A, (Γ+Δ)\\
    (x :_p A,Γ) + Δ &= x :_p A, Γ+Δ & (x ∉ Δ)\\
    () + Δ &= Δ
  \end{align*}
\end{definition}
\noindent
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

These operations depend, in turn, on addition and multiplication of multiplicities.
The syntax of multiplicities is given in \fref{fig:syntax}.
We need the concrete multiplicities $1$ and $ω$ and, to support polymorphism,
multiplicity variables (ranged over by the metasyntactic
variables \(π\) and \(ρ\)).  Because we
need to multiply and add multiplicities,
we also need formal sums and products of multiplicities.
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

The variable rule (var) uses a standard idiom:
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
multiplicity $p$; this is analogous to the explicit
multiplicity on a $\mathsf{let}$ binding.  It says how often the scrutinee (or,
for a $\mathsf{let}$, the right hand side) will be consumed.  Just as
for $\mathsf{let}$, we expect $p$ to be inferred from an un-annotated $\mathsf{case}$ in
\HaskeLL{}.

The scrutinee $t$ is consumed $p$ times, which accounts for the $pΓ$ in
the conclusion.  Now consider the bindings $(x_i :_{pq_i[p_1…p_n]} A_i)$ in the
environment for typechecking $u_k$.  That binding will be linear only if
\emph{both} $p$ \emph{and} $q_i$ are linear; that is, only if we specify
that the scrutinee is consumed once, and the $i$'th field of the data constructor $c_k$
specifies that is it consumed once if the constructor is (\fref{def:consume}).

To put it another way, suppose one of the linear
fields\footnote{
Recall \fref{sec:non-linear-constructors}, which described
how each constructor can have a mixture of linear and non-linear fields).}
of $c_k$ is used non-linearly in $u_k$.  Then, $q_i=1$ (it is a linear field),
so $p$ must be $ω$, so that $pq_i=ω$.  In short, using a linear field non-linearly
forces the strutinee to be used non-linearly, which is just what we want.
Here are some concrete examples:
\begin{code}
  fst  ::  (a,b) →  a     bigSpace    swap ::  (a,b) ⊸ (b,a)
  fst      (a,b)  =  a                swap     (a,b) =  (b,a)
\end{code}
Recall that both fields of a pair are linear (\fref{sec:linear-constructors}).
In |fst|, the second component of the pair is used non-linearly (by being
discarded) which forces the use of $\mathsf{case}_ω$, and hence a non-linear type
for |fst|.  But |swap| uses the components linearly, so we can use $\mathsf{case}_1$, giving
|swap| a linear type.

\subsection{Metatheory}
\label{sec:metatheory}

The details of meta-theory of \calc{} are deferred to
\fref{appendix:dynamics}. Our goal is to establish two properties:
\begin{itemize}
\item That a pure linear interface can be implemented using mutations
  under the hood.
\item That the ``typestate'' of data is enforced by the type system\jp{what does this mean? what is a typestate?}
\end{itemize}

To that effect we introduce two semantics: a semantic with
mutation where type-states are enforced dynamically and a pure semantics
that tracks linearity carefully, but where ``mutations'' are
implemented as copying. Both semantics are big step operational
semantics with laziness in the style of \citet{launchbury_natural_1993}.

The semantics are instantiated with the arrays of
\fref{sec:freezing-arrays}. They can be easily extended to support,
for instance, a real-world token and file handles like in
\fref{sec:io-protocols}.

We then prove the two semantics to be bisimilar from which we can
deduce:
\begin{theorem}
  The implementation of the array primitives with in-place mutation is
  observationally equivalent to a pure implementation.
\end{theorem}
\begin{theorem}
  Neither semantics can block on typestates. Therefore typestates need
  not be tracked dynamically.
\end{theorem}

The complete proof of both of these statements can be found in
\fref{appendix:dynamics}.

\subsection{Design choices \& trade-offs}
Let us review the design space allowed by \calc{}, the points that we
chose, and the generalizations that we have left open.

\paragraph{Case rule}\unsure{While I was writing this new version,
  Simon suggested that we canned the discussion on $\varid{case}_ω$
  altogether. Let's discuss that soon.}
It is possible to do without $\varid{case}_ω$, and have only $\varid{case}_1$.
Consider |fst| again.  We could instead have
\begin{code}
data (,) p q a b where
  (,) :: a → _ p b → _ q (,) p q a b

fst :: (,) 1 ω a b ⊸ a
fst x = case_1 x of (,) a b -> a
\end{code}
But now linearity polymorphism infects all basic data types (such as pairs), and it
it hard to forsee all the consequences.  Moreover, |let| is annotated so it seems
reasonable to annotate |case| in the same way.

To put it another way, our design choice allows to meaningfully inhabit
|Unrestricted (a,b) ⊸ (Unrestricted a, Unrestricted b)|, while linear logic
forbids that.

\unsure{aspiwack: we could add that, interestingly, the regular tensor
product of linear logic, where the components must be consumed the
same number of times can be recovered as |type a ⊗ b = forall r. ((a,b)⊸r)⊸r|.}

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
guarantees than |g| requires.  However, eta-expansion to |g (\x. f x)|
makes the expression typeable, as the reader may check.
Alternatively, |g| might well be multiplicity-polymorphic, with type
|forall π. (Int -> _ π) -> Bool|; in which case |(g f)| is, indeed, typeable.
\jp{I feel that the eta-expansion thing is enough discussion. I
  suggest that we can say that extending subtyping is future work.}

The lack of subtyping is a deliberate choice in our design: it is well
known that Hindley-Milner-style type inference does not mesh well with
subtyping (see, for example, the extensive exposition by
\citet{pottier_subtyping_1998}).

\paragraph{Polymorphism} Consider the definition
\begin{code}
id x = x
\end{code}
Our typing rules would validate both |id :: Int → Int| and |id :: Int ⊸ Int|.
So, since we think of multiplicities ranging over $\{1,ω\}$, surely we should
also have |id :: forall π. Int → _ π Int|?  But as it stands, our rules do
not accept it. To do so we would need $x :_π Int ⊢ x : Int$.  Looking
at the (var) rule in \fref{fig:typing}, we can prove that premise by case analysis,
trying $π=1$ and $π=ω$.
\simon{I could not work out what your $π$ and $π'$ were.... so I ended up with case analysis.  What am I missing?}
But if we had a richer domain of multiplicities, including
$0$\footnote{\citet{mcbride_rig_2016} uses 0-multiplicities to express runtime irrelevance
in a dependently typed system}
or $2$ for example, we would be able to prove $x :_π Int ⊢ x : Int$, and rightly
so becuase it is not the case that |id :: Int → _ 0 Int|.

For now, we accept more conservative rules, in order to hold open the possiblity
of extending the multiplicity domain later.  But there is an up-front cost,
of somewhat less polymorphism than we might expect.  We hope that experience will
lead us to a better assessment of the costs/benefit tradeoff here.

\section{Applications}
\label{sec:evaluation}

Implemented using our branch of the \textsc{ghc} compiler described in
\fref{sec:implementation}\improvement{Needs an introductory paragraph}

\subsection{Serialised tree traversals}
\label{sec:cursors}

Let us look back to the array-freezing \textsc{api} of
\fref{sec:freezing-arrays}. An push the boundaries to a new range of
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
\fref{sec:freezing-array}. However, there are further things to
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

\subsection{Sockets with type-level state}
\label{sec:sockets}

The \textsc{bsd} socket \textsc{api} is a standard, if not \emph{the}
standard, through which computer connect over networks. It involves a
series of actions which must be performed in order: on the
server-side, a freshly created socket must be \emph{bound} to an
address, then start \emph{listening} incoming traffic, then
\emph{accept} connection requests, said connection is returned as a
new socket, this new socket can now \emph{receive} traffic. One reason
for having that many actions to do is that the precise sequence of
action is protocol-dependent. For \textsc{tcp} traffic you would do as
described, but for \textsc{udp}, which does not need connections, you
would not accept connection but receive messages directly. The
\texttt{socket} library for Haskell, exposes precisely this sequence
of actions.

It is a bit clumsy to program with: with each action, not only the
state of the socket changes, but also the actions permissible on
this. Used as we are to typed programming languages, we like to use
type to predicate what actions can be taken on an object. So the state
of sockets should be tracked in the type. This is akin to a typestate
analysis~\cite{strom_typestate_1983}.

In the |File| \textsc{api} of \fref{sec:io-protocols}, we made files
safer to use at the cost of having to thread a file handle
explicitely: each function consumes a file handle and returns a fresh
one. We can make this cost into an opporunity: we have the option of
returning a handle \emph{with a different type} from that of the
handle we consumed! So by adjoining a phantom type to sockets to track
their state, we can effectively encode the proper sequencing of socket
actions.

As an illustration, we implemented wrapper around the \textsc{api} of the
\texttt{socket} library. For the sake of simplicity this wrapper is
specialised for the case of \textsc{tcp}.

\begin{code}
data State = Unbound | Bound | Listening | Ingress | Egress
data Socket (s :: State)
data SocketAddress

socket ::  IOL 1 (Socket Unbound)
bind ::  Socket Unbound ⊸ SocketAddress -> IOL 1 (Socket Bound)
listen :: Socket Bound ⊸ IOL 1 (Socket Listening)
accept ::  Socket Listening ⊸ IOL 1 (Socket Listening, Socket Egress)
connect ::  Socket Unbound ⊸ SocketAddress -> IOL 1 (Socket Ingress)
send :: Socket Ingress ⊸ ByteString -> IOL 1 (Socket Ingress, Unrestricted Int)
receive :: Socket Egress ⊸ IOL 1 (Socket Egress, Unrestricted ByteString)
close :: forall s. Socket s -> IOL ω ()
\end{code}

This linear socket \textsc{api} is very similar to files': we use the
|IO_L| monad in order to enforce linear use of sockets. The difference
is the argument to |Socket|, which represent the current state of the
socket and is used to limit the functions which can apply to a socket
at a given time.

\subsection{Pure bindings to impure APIs}
\label{sec:spritekit}

\Citet{chakravarty_spritekit_2017} have a different kind of
problem. \Citeauthor{chakravarty_spritekit_2017} are building a pure
interface for graphical interfaces, in the same style as the Elm
programming language\improvement{citation}, but are implementing it in
terms of an existing imperative graphical interface engine.

Basically, the pure interface takes an update function |Scene ->
Scene| which is tasked with returning the next state that the
interface will display. In order to efficiently map this pure
interface to the imperative engine, the new |Scene| must not destroy
the entire imperative scene and re-create it, but must be rendered
using imperative update. To achieve this result, the nodes in the
|Scene| data-type contain pointers to the imperative nodes that they
represent, so that changing, say, a node |np|'s children will be
effected as an imperative update of the corresponding imperative node
|ni|.

But if the update function duplicates |ni|, the imperative update will
mutate |ni| twice. Which would break the pure semantics. In the
current state of the implementation, the programmer must be careful of
not duplicating |ni|. Linear types offer a solution where the
programmer cannot inadvertently break that promise: we take the update
function to be of type |Scene ⊸ Scene|. With such a linear update
function duplication of |ni| becomes impossible, and if a |np| must be
duplicated, only one of the duplicates will have a reference to |ni|.

We have implemented a simplified version of this solution in the case
where the impure \textsc{api} is a simple tree
\textsc{api}.\improvement{With some data regarding implementation, a
  remark that linearity is not used \emph{in} the implementation but
  only as the interface level to ensure that the proof obligation is
  respected by the \textsc{api} user.}

\subsection{Feedback from industrial experience}

\todo{Tweag to give some short descriptions of situations where linear
  types are desirable from actual industrial work}

\section{Implementing \HaskeLL}
\label{sec:implementation}
\label{sec:impl}

We are implementing \HaskeLL{} as a branch over the 8.2 version
\textsc{ghc}, the leading Haskell compiler. At time of writing this
branch only modifies the type inference of the compiler, neither the
intermediate language (Core\improvement{citation for Core}) nor the
run-time system are affected. We have only implemented monomorphic
multiplicities so far. Our \HaskeLL{} implementation is not compatible
with every \textsc{ghc} extension yet, but is compatible with
standardised Haskell\unsure{This ought to be checked} as well as many
extensions.

In order to implement the linear arrow, we followed the design of
\calc{} and added a multiplicity annotation to arrows, as an
additional argument of the type constructor for arrows of
\textsc{ghc}'s type checker. The constructor for arrow types is
constructed and destructed a lot in \textsc{ghc}'s type checker, this
accounts for most of the modifications to existing code.

Where the implementation defers from \calc{} is the way multiplicity
are computed: whereas in the \calc{} multiplicities are inputs of the
type-checking algorithm, in the implementation multiplicities are
outputs of type inference. The main reason for this choice is that it
makes prevents us from having to split the context along
multiplicities (for instance in the application rule), which would
have been achieved, in practice, by extending the semi-ring structure
with partial operations for subtraction and division.

Instead, in the application rule, we get the multiplicities of the
variables in each of the operands as inputs and we can add them
together. We still need to require more than just a semi-ring though:
we need an ordering of the multiplicity semi-ring (such that
$1\leqslant ω$) in order to check that the computed multiplicity is
correct with respect to multiplicity annotations. In addition to the
ordering, we need to be able to join the multiplicity computed in the
branches of a |case|. To that effect, we need a supremum
operation. Therefore the multiplicities need to form a
join-semi-lattice-ordered semi-ring.

Implementing this branch affects 1122 lines of \textsc{ghc} (for
comparison the parts of the compiler that were affected by \HaskeLL{}
total about 100000 lines of code), including 436 net extra lines. A new
file responsible for multiplicity operations as well the files
responsible for type environment manipulation and type inference of
patterns account for almost half of the affected lines. The rest spans
over a 100 files most of which have 2 or 3 lines modified to account
for the extra multiplicity argument of the arrow constructor. This
required roughly 1 man-month to implement.

These figures vindicate our claim that \HaskeLL{} is easy to integrate
into an existing implementation: despite \textsc{ghc} being 25 years
old, we could implement a first version of \HaskeLL{} with relatively
low effort.

\improvement{Our branch has been used to implement…}

\section{Related work}
\label{sec:related}
\subsection{Region-types}

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
% arnaud: The stack story is true, but it is not an easy case to make,
% so I've taken it out for now. General idea is: in |ST| you can use
% values as long as their regions lives, so resources can't be closed
% before |runST| has completed. Whereas with linear types, we can
% "disappear" a value, at which time we can take the opportunity to
% close it. It is hard, however to pinpoint a case where it is
% critical not to use stack-allocation.

% jp: In many pipeline applications one has conceptually n
% buffers used sequentially, but only two of them are live
% simultaneously.

\item |ST|-like regions confine to a stack-like allocation discipline,
  because freeing resources coincide with the static scope of |runST|.
  Thus lifetimes cannot intersect arbitrarily, limiting the applicability of
  this technique. This factor is a limitating for any long-lived
  program, but in particular, in many pipeline applications one has
  conceptually |n| buffers used sequentially, but only two of them are
  live simultaneously.

  In our system, even though the lifetimes of linear variables is
  checked statically, we can make use of continuation-passing style
  (or Monads) to implement dynamic lifetimes for objects in the linear
  heap.  Consider for example the primitives |alloc : (A ⊸ r) ⊸ r| and 
|free  : A ⊸ r ⊸ r|.
We can write code such as the following, where the lifetimes of |x|, |y|
and |z| overlap in a non-stack fashion:
\begin{code}
alloc  (\x ->
{- x live -}
alloc  (\y ->
{- x and y live -}
free x (
alloc  (\z ->
{- y and z live -}
free y (
{- z live -}
free z)))))
\end{code}

\item |ST| actions cannot be interleaved with |IO| actions. So in our
  mutable array examples, for instance, it is not possible to provide
  a safe abstraction around |unsafeFreeze :: MArray s a -> ST s (Array
  a)| which will also make it possible to use |IO| actions to fill in
  the array.\jp{I do not understand this item.}
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
  reuse, forces otherwise pure functions to be written monadically and
  rules out useful syntactic facilities like view patterns. In
  contrast, with linear types, values in two regions (in our running
  example packets from different mailboxes) have the same type hence
  can safely be mixed: any data structure containing packet of
  a mailbox will be forced to be consumed before the mailbox is
  closed.\jp{FIXME: running example is now gone.}
\end{itemize}

\subsection{Uniqueness and ownership typing}

The literature is awash with enforcing linearity not via linear types,
but via uniqueness (or ownership) types. The most prominent
representatives of languages with uniqueness types are perhaps
Clean~\cite{barendsen_uniqueness_1993} and
Rust~\cite{matsakis_rust_2014}. \HaskeLL, on the other hand, is
designed around linear types based on linear
logic~\cite{girard_linear_1987}.

Linear types and uniqueness types are, at their core, dual: whereas a linear type is
a contract that a function uses its argument exactly once
even if the call's context can share a linear argument as many times as it
pleases, a uniqueness type ensures that the argument of a function is
not used anywhere else in the expressions context even if the function
can work with the argument as it pleases.

Seen as a system of constraints, uniqueness typing is a {\em non-aliasing
analysis} while linear typing provides a {\em cardinality analysis}. The
former aims at in-place updates and related optimisations, the latter
at inlining and fusion. Rust and Clean largely explore the
consequences of uniqueness on in-place update; an in-depth exploration
of linear types in relation with fusion can be found
in~\citet{bernardy_composable_2015}, see also the discussion in
\fref{sec:fusion}.\unsure{The discussion on fusion may well disappear}

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

\paragraph{Rust}
Rust \cite{matsakis_rust_2014} features a variant of uniquness typing, called ownership
typing. Like the original formulation of linear logic, in Rust \texttt{A}
stands for linear values, unrestricted values at type \texttt{A} are denoted
\texttt{RC<A>}, and duplication is explicit.

\jp{It is not clear why this applies to Rust only and not other uniqueness typing systems.}
Rust addresses the problem of being mindful about
memory, resources, and latency, but this comes at a price: Rust,
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
regular non-linear expressions are the norm, yet gracefully scaling up
to latency-sensitive and resource-sensitive programs is still
possible.\improvement{Change depending on what we put in the
  evaluation section}

\paragraph{Borrowing}
How can borrowing be encoded in \HaskeLL{}? Instead of tracking the
lifetime of references using a special system, one can simply give
each reference a multiplicity of one, and explicitly pass them around.

A function can be declared to destroy a reference simply by taking it
as a (linear) parameter.  For example the following signature is that
of a function from |A| to |B| which also destroys a reference:
\begin{code}
destroyer : Reference ⊸ A -> B
\end{code}
A function which borrows a reference can take it as input and return
it.
\begin{code}
borrower : Reference ⊸ A -> (Reference, B)
\end{code}
\paragraph{Borrowing references in data structures}
In an imperative language, one often walks data structure, extract
references and pass them around. In Rust, the borrowing system
ensures that the passed reference does not outlive the datastructure
that it points to.

In a functional language, instead of extracting references, one will
use lenses to lift a modification function from a local subtree to a
global one. Thanks to garbage collection, there is already no risk of
dangling references, but one has to pay a runtime cost. By using
linear types one can avoid this cost.

Indeed, we can ensure that a modification function can have the type:
|Reference ⊸ Reference| and thus can be implemented with no need for
GC. At the same time, the lens library will use linear types and lift
local linear modifications to global linear modifications. Note that,
if the original object lives in the GC heap (and thus can be shared),
the same lens library can be used, but individual lifting of
modifications cannot be implemented by in-place update.

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
kind. Values with a type whose kind is linear are be linear, and the
others are unrestricted.  In a typical design making this choice,
every type constructor exists in two flavours: one which constructs a
linear type and one which constructs an unrestricted type. (Thus in
particular such systems feature ``linear arrows'', but they have a
completely different interpretation from ours.)

An advantage of ``linearity via kinds'' is the possibility to directly
declare the linearity of values returned by a function---not just that
of the argument of a function. In contrast, in our system if one wants
to indicate that a returned value is to be used linearly, we have to
use a double-negation trick. That is, given $f : A → (B ⊸ !r) ⊸ r$,
then $B$ can be used a single time in the (single) continuation, and
effectively $f$ ``returns'' a single $B$. One can obviously declare a
type for linear values |Linear a = (a ⊸ !r) ⊸ r| and chain
|Linear|-returning functions with appropriate combinators.  In fact,
as explained in \fref{sec:linear-io}, the cost of the double negation
almost entirely vanishes in the presence of an ambient monad.

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

Advantages of ``linearity via arrows'' include:

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
    (++) :: [a] ⊸ [a] ⊸ [a]
    cycle :: [a] → [a]
  \end{code}
  The following definition type-checks, even though |++| is applied to
  unrestricted values and used in an unrestricted context.
  \begin{code}
    f :: [a] → [a] → [a]
    f xs ys = cycle (xs ++ ys)
  \end{code}
  In contrast, in a two-kind system, a function must declare
  the \emph{exact} linearity of its return value. Consequently, to make a function
  promotable from linear to unrestriced, its declaration must use
  polymorphism over kinds.

\item Easier polymorphism.  Even in the cases where code-sharing requires
  to use polymorphism, linearity on arrows is simpler to use.  Indeed,
  linearity polymorphism can be supported by adding a special-purpose
  quantification, which is syntactically separate and does not
  interfere with any other aspect of the type-system. In contrast, if
  linearity is encoded in kinds, one needs
  kind-polymorphism. Furthermore, the subsumption property must be
  encoded via a sub-kinding property, which is not easy to get right,
  especially in the presence of ML-style polymorphism. The difficulty
  is witnessed in the work of \citet{morris_best_2016}: several of
  applications (including monads) require bounded polymorphism, while
  we can avoid it here.

\item Exensibility.  It is easy to extend our system to any set of
  ground multiplicities with a ring structure
  (\fref{sec:extending-multiplicities}), which is useful to support
  for example affine types and dependent linear types.  In contrast,
  in a multiple-kind system, such extensions require \textit{ad-hoc}
  support. Indeed, affine types require changes in the subkinding
  system, which in turns may impact unification. While there exists
  systems with two-kinds and dependent types, they are only trivial in
  the sense that no linear arrow can be dependent.

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

\item Easier implementation. We managed to implement a working
  prototype of \textsc{ghc} linearity-on-arrow, and our patch is only a little
  over 1000loc. We attribute its relative simplicity to two factors.
  First, we could avoid tracking of the kind of types in the
  variables, which is a daunting task in \textsc{ghc}'s type-checker \jp{why?}.

  Second, \textsc{ghc} already supports impredicative dependent types
  and a wealth of unboxed or otherwise primitive types and kinds that
  cannot be substituted for polymorphic type arguments. Further extending
  the kind system is a complex endeavour which we could avoid entirely.
\end{itemize}

% Such approaches have been very successful for theory: see for instance
% the line of work on so-called \emph{mixed linear and non-linear logic}
% (usually abbreviated \textsc{lnl}) started by
% \citet{benton_mixed_1995}.

% JP: I don't know what theory this refers to. Also I do not believe
% that this is relevant for this paper.



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
This derivation is not desirable: it implies that there cannot be
reusable definitions of linear functions. In terms of linear logic~\cite{girard_linear_1987},
\citeauthor{mcbride_rig_2016} makes the natural function of type $!(A⊸B) ⟹ !A⊸!B$
into an isomorphism.
In that respect, our system is closer to
\citeauthor{ghica_bounded_2014}'s.

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

\subsection{Operational aspects of linear languages}

\improvement{Not the right place, but let us not forget to cite the
  very relevant: \cite{pottier_programming_2013}}
\unsure{This section will need a clean up, to be more in phase of what
we present in the evaluation section}

\Citet{wakeling_linearity_1991} produced a complete implementation of
a language with linear types, with the goal of improving the
performance. Their implementation features a separate linear heap, as
\fref{appendix:dynamics} where they allocate as much as possible in the
linear heap, as modelled by the strengthened semantics. However,
\citeauthor{wakeling_linearity_1991} did not manage to obtain
consistent performance gains. On the other hand, they still manage to
reduce \textsc{gc} usage, which may be critical in distributed and
real-time environments, where latency that matters more than
throughput.

\citeauthor{wakeling_linearity_1991} propose to not attempt prompt
free of thunks and only taking advantage of linearity for managing the
lifetimes of large arrays. Our approach is similar: we advocate
exploiting linearity for operational gains on large data structures
(but not just arrays) stored off-heap. we go further and leave the
management of external (linear) data to external code, only accessing
it via an \textsc{api}. Yet, our language supports an implementation
where each individual constructor with multiplicity 1 can be allocated
on a linear heap, and deallocated when it is pattern matched.
Implementing this behaviour is left for future work.

\subsubsection{Garbage}
\citet{mogensen_types_1997} proposes a type system whose purpose is to
track the number of times that a value is used. They intend their
system to be used for inference instead of declaration. Thus, while
our main concern is the smooth integration with an existing lazy
functional language, they do not pay any attention to any language
design issue. Besides, their system features both annotations on types
an certain variable bindings: while our type-system is related to
theirs it appears to be incomparable.

The work of \citet{igarashi_garbage_2000} uses the typesystem of
Mogensen to drive a garbage collection mechanism. Yet, their approach
is opposite to ours: while we aim to keep linear values
completely outside of garbage collection, they use the type
information at runtime to ensure that the GC does not follow dangling
pointers.
% JP: How can that even work?

\section{Conclusion and future work}

This article demonstrated how an existing lazy language, such
as Haskell, can be extended with linear types, without compromising
the language, in the sense that:
\begin{itemize}
\item existing programs are valid in the extended language
  \emph{without modification},
\item such programs retain the same semantics, and
\item the performance of existing programs is not affected,
\item yet existing library functions can be reused to serve the
  objectives of resource sensitive programs with simple changes to
  their types without being duplicated.\unsure{Do we still speak of
    resource sensitivity all that much?}
\end{itemize}
In other words: regular Haskell comes first. Additionally, first-order
linearly typed functions and data structures are usable directly from
regular Haskell code. In such a setting their semantics is that of
the same code with linearity erased.

\HaskeLL{} was engineered as an unintrusive design, making it tractable
to integrate to an existing, mature compiler with a large ecosystem.
We have developed a prototype implementation extending
\textsc{ghc} with multiplicities. The main difference between the
implementation and \calc is that the implementation is adapted to
bidirectionality:\jp{the typing rules do not dictate an algorithm, so this is not a difference. In fact it says above ``One may want to think of the \emph{types} in $Γ$ as
inputs of the judgement, and the \emph{multiplicities} as outputs.''}
typing contexts go in, inferred multiplicities come
out (and are compared to their expected values). As we hoped, this
design integrates very well in \textsc{ghc}.

\improvement{We don't talk about the ffi all that much in this version
I think. This paragraph ought to be adapted to match the content of
the evaluation section.}
It is worth stressing that, in order to implement foreign data
structures like we advocate as a means to
provide safe access to resources or reduce \textsc{gc} pressure and
latency, we only need to modify the type system: primitives to
manipulate foreign data can be implemented in user libraries using the
foreign function interface. This helps keeping the prototype lean,
since \textsc{ghc}'s runtime system (\textsc{rts}) is unaffected.

\todo{Section on the |newtype Unrestricted| problem. I guess?}

\subsection{Inlining}
\label{sec:fusion}

\improvement{This section seems to be unclear. Either too long or too
  short.}  Inlining is a staple of program optimisation, exposing
opportunities for many program transformations including fusion. Not
every function can be inlined without negative effects on performance:
inlining a function with more than one use sites of the argument may
result in duplicating a computation. For example one should avoid the
following reduction: |(\x -> x ++ x ) expensive ⟶ expensive ++
expensive|.

Many compilers can discover safe inlining opportunities by analysing
the source code in order to determine how many times functions use
their arguments.  (In \textsc{ghc} this analysis is called a
cardinality analysis~\cite{sergey_cardinality_2014}). The limitation
of such an analysis is that it is necessarily heuristic (the problem
is undecidable). Because inlining is crucial to efficiency,
programmers find themselves in the uncomfortable position of relying
on a heuristic to obtain efficient programs. A small, seemingly
innocuous change can prevent a critical inlining opportunity and have
rippling effects throughout the program.  Thus folklore is that
high-level languages should be abandonned if one wants control over
the performance.

Linear types address this issue by serving as a programmer-facing
interface to inlining: because it is always safe to inline a linear
function, we can make it part of the \emph{semantics} of linear
functions that they are always inlined. In fact, the system of
multiplicity annotation of \calc{} can be faithfully embedded the
abstract domain presented by \citet{sergey_cardinality_2014}. This
gives confidence in that linear arrows can serve as
cardinality \emph{declarations}.

Formalising and implementing the integration of multiplicity
annotation in the cardinality analysis is left as future work.

\subsection{Extending multiplicities}
\label{sec:extending-multiplicities}

% Applications of multiplicities beyond linear logic seem to often have
% too narrow a focus to have their place in a general purpose language
% such as Haskell. \Citet{ghica_bounded_2014} propose to use
% multiplicities to represent real time annotations, and
% \citet{petricek_coeffects_2013} show how to use multiplicities to
% track either implicit parameters (\emph{i.e.} dynamically scoped
% variables) or the size of the history that a dataflow program needs to
% remember. \jp{I think that it would be enough to list the useful extensions (dependent and affine types.)}

\improvement{This section could speak about the borrowing
  multiplicity.}  For the sake of this article, we use only $1$ and
$ω$ as possibilities.  But in fact \calc{} can readily be extended to
more multiplicities: we can follow \citet{ghica_bounded_2014} and
\citet{mcbride_rig_2016}. The general setting for \calc{} is an
ordered-semiring of multiplicities (with a join operation for type
inference).  In particular, in order to support dependent types, we
additionally need a $0$ multiplicity. We may may want to add a
multiplicity for affine arguments (\emph{i.e.}  arguments which can be
used \emph{at most once}).

The typing rules are mostly unchanged with the \emph{caveat} that
$\mathsf{case}_q$ must exclude $q=0$ (in particular we see that we
cannot substitute multiplicity variables by $0$). The variable rule is
modified as:
$$
\inferrule{ x :_1 A \leqslant Γ }{Γ ⊢ x : A}
$$
Where the order on contexts is the point-wise extension of the order
on multiplicities.

%% Acknowledgments
\begin{acks}                            %% acks environment is optional
                                        %% contents suppressed with 'anonymous'
  %% Commands \grantsponsor{<sponsorID>}{<name>}{<url>} and
  %% \grantnum[<url>]{<sponsorID>}{<number>} should be used to
  %% acknowledge financial support and will be used by metadata
  %% extraction tools.
  This work has received funding from the European Commission
  through the SAGE project (grant agreement no. 671500).
\end{acks}

%% Bibliography
\bibliography{../PaperTools/bibtex/jp.bib,../local.bib}{}


%% Appendix
\appendix
\section{Semantics and soundness of \calc{}}
\label{appendix:dynamics}

\newcommand{\termsOf}[1]{\mathnormal{terms}(#1)}
\newcommand{\multiplicatedTypes}[1]{\bigotimes(#1)}
\newcommand{\ta}[2]{γ(#1)(#2)}


\unsure{aspiwack: I ignored the multiplicity polymorphism as it is
  really of no consequence as long as we don't take higher-rank
  multiplicity functions. That being said, we speak of multiplicity
  polymorphism quite a bit. Maybe we can just add them back into the
  dynamics. The proof, apart from the primitive functions, is trivial
  anyway.}
\improvement{aspiwack: In the rules for primitives, I tend to omit the reduction
of the strict arguments (shuch as indices of arrays). I should
probably fix this.}
\improvement{aspiwack: (related with the strictness thing) In the rule
  for |write|, I use |l| directly where I should use a variable
  |x| that points to |l|}
\improvement{aspiwack: in the |newMArray| rule, I use an illegal form
  of application. It is straightforward to put in in let-form as is
  required by the Launchbury semantics, but it should be done. In the
  |freeze| rule I do the same, but in the return type. Can I
  reuse the variable carrying the array in the left-hand side
  (currently omitted, see above) to avoid the complication of creating
  a new variable? I think so.}
\improvement{aspiwack: we at least need a |read| primitive on frozen
|Array|-s.}

Following \citet{gunter_partial-big-step_1993}, we consider not only
standard big-step derivation but also partial derivations. This
require some additional setup compared to standard presentation of
big-step semantics (in particular compared to
\citet{launchbury_natural_1993}): schematically, to ensure that the
right-hand side of the reduction relation never is never
pattern-matched, we introduce, in addition to the usual big-step
relation $a⇓b$ an additional relation, that we write $a⇒b$, whose role
is to reduce one redex.\improvement{aspiwack: actually do that in the
  rules, or maybe I don't actually need it}

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

\begin{figure}
  \figuresection{Translation of typed terms}
  \begin{align*}
    (λ_q(x{:}A). t)^* &= λ_q(x{:}A). (t)^* \\
    x^*             &= x \\
    (t  x )^*     &= (t)^*  x \\
    (t  u )^*     &= \flet[q] y : A = (u)^* \fin (t)^*  y &
    \text{with $Γ⊢ t : A →_q B$}
  \end{align*}
  \begin{align*}
    c_k  t₁ … t_n   &= \flet x₁ :_{q_1} A_1 = (t₁)^*,…, x_n :_{q_n} A_n = (t_n)^*
                      \fin c_k x₁ … x_n & \text{with $c_k : A_1
                                          →_{q_1}…A_n →_{q_n}D$}
  \end{align*}
  \begin{align*}
    (\case[p] t {c_k  x₁ … x_{n_k} → u_k})^* &= \case[p] {(t)^*} {c_k  x₁ … x_{n_k} → (u_k)^*} \\
    (\flet[q] x_1: A_1= t₁  …  x_n : A_n = t_n \fin u)^* & = \flet[q] x₁:A_1 = (t₁)^*,…, x_n:A_n= (t_n)^* \fin (u)^*
  \end{align*}

  \caption{Syntax for the Launchbury-style semantics}
  \label{fig:launchbury:syntax}
\end{figure}

\begin{figure}
  \begin{mathpar}
    \inferrule{ }{Γ : λ_p(x{:}A). e ⇓ Γ : λ_p(x{:}A). e}\text{abs}


    \inferrule{Γ : e ⇓ Δ : λ_p(y{:}A).e' \\ Δ : e'[x/y] ⇓ Θ : z} {Γ :
      e x ⇓ Θ : z} \text{application}

    \inferrule{Γ : e ⇓ Δ : z}{(Γ,x :_ω A = e) : x ⇓ (Δ;x :_ω A = z) :
      z}\text{variable}

    \inferrule{ }
    {(Γ,l :_1 A = z) : l ⇓ (Δ, l :_1 A = z) : l}\text{mutable cell}

    \inferrule{(Γ,x_1 :_ω A_1 = e_1,…,x_n :_ω A_n e_n) : e ⇓ Δ : z}
    {Γ : \flet[q] x₁ : A_1 = e₁ … x_n : A_n = e_n \fin e ⇓ Δ :
      z}\text{let}

    \inferrule{ }{Γ : c  x₁ … x_n ⇓ Γ : c  x₁ …
      x_n}\text{constructor}


    \inferrule{Γ: e ⇓ Δ : c_k  x₁ … x_n \\ Δ : e_k[x_i/y_i] ⇓ Θ : z}
    {Γ : \case[q] e {c_k  y₁ … y_n ↦ e_k } ⇓ Θ : z}\text{case}

    %%%% Arrays

    \inferrule
    {(Γ, l :_1 \varid{MArray}~a = [a,…,a]) : f~l ⇓ Δ : \varid{Unrestricted}~x}
    {Γ : \varid{newMArray}~i~a~f ⇓ Δ : \varid{Unrestricted}~x}\text{newMArray}

    \inferrule{ }
    {(Γ,l:_1 \varid{MArray}~a = [a_1,…,a_i,…,a_n]) :
      \varid{write}~l~i~a ⇓ Γ,l :_1 \varid{MArray}~a =
      [a_1,…,a,…,a_n] : l}\text{write}

    \inferrule{ }
    { (Γ,l :_1 \varid{MArray}~a = [a_1,…,a_n]) : \varid{freeze}~l ⇓ (Γ,l :_1 \varid{Array}~a = [a_1,…,a_n]) :
      \varid{Unrestricted}~l}\text{freeze}


    %%%% /Arrays
  \end{mathpar}

  \caption{Dynamic semantics}
  \label{fig:dynamics}
\end{figure}

\begin{figure}
  \begin{mathpar}
\inferrule{ }{Ξ ⊢ (Γ || λ_q(x{:}A). e ⇓ Γ || λ_q (x{:}A). e) :_ρ A→_q B, Σ}\text{abs}

\inferrule
    {Ξ  ⊢  (Γ||e      ⇓ Δ||λ(y:_q A).u):_ρ A →_q B, x:_{qρ} A, Σ \\
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
  {Ξ ⊢ (Γ,       x_1 :_{ρq} A_1 = e_1 … x_n :_{ρq} A_n = e_n  ||  t ⇓ Δ||z) :_ρ C, Σ}
  {Ξ ⊢ (Γ||\flet[q] x_1 :  A_1 = e_1 … x_n : A_n = e_n \fin t ⇓ Δ||z) :_ρ C, Σ}
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

%%%%% Arrays

\inferrule
{Ξ ⊢ (Γ||f~[a,…,a]) ⇓ Δ||\varid{Unrestricted}~x) :_1 \varid{Unrestricted}~B, Σ}
{Ξ ⊢ (Γ||\varid{newMArray}~i~a~f ⇓ Δ||\varid{Unrestricted}~x) :_ρ \varid{Unrestricted}~B, Σ}\text{newMArray}

\inferrule
{ }
{Ξ ⊢ (Γ,x:_1 \varid{MArray}~a = [a_1,…,a_i,…,a_n]||\varid{write}~x~i~a
  ⇓ Γ||[a_1,…,a,…,a_n]) :_1 \varid{MArray}~a, Σ)}\text{write}

\inferrule
{ }
{Ξ ⊢ (Γ,x:_1 \varid{MArray}~a = [a_1,…,a_n]||\varid{freeze}~a ⇓ Γ||\varid{Unrestricted}
  [a_1,…,a_n]) :_1 \varid{Unrestricted} (\varid{Array}~a), Σ}\text{freeze}

%%%% /Arrays
  \end{mathpar}
  \caption{Denotational dynamic semantics}
  \label{fig:typed-semop}
\end{figure}

\begin{definition}[Annotated state]
  \improvement{Maybe change the name from ``annotated''. Also, the
    values are a bit different as we have values for arrays, whereas
    previously they were only in linear bindings of the }

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
  bindings\improvement{needs more effort in our restricted $\flet[q]$ calculus}, $\termsOf{e_1 :_{ρ_1} A_1, … , e_n :_{ρ_n} A_n}$
  for $(e_1~{}_{ρ_1}\!, (…, (e_n~{}_{ρ_n},())))$, and
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
\end{definition}

\begin{lemma}[Denotational reduction preserves typing]\label{lem:type-safety}
  If  $Ξ ⊢ (Γ||t ⇓ Δ||z) :_ρ A, Σ$, or $Ξ ⊢ (Γ||t ⇓ Δ||z) :_ρ A, Σ$ then
  $$
  Ξ ⊢ (Γ||t :_ρ A),Σ \text{\quad{}implies\quad{}} Ξ ⊢ (Δ||z :_ρ A),Σ.
  $$
\end{lemma}
\begin{proof}
  By induction on the typed-reduction.
\end{proof}

\begin{definition}[Denotation assignment]
  A well-typed state is said to be a denotation assignment for an ordinary
  state, written $\ta{Γ:e}{Ξ ⊢ Γ' || e' :_ρ A , Σ}$, if
  $e[Γ_1]=e' ∧ Γ' \leqslant Γ_ω[Γ_1]$.\improvement{explain the
    restrictions of $Γ$}

  That is, $Γ'$ is allowed to strengthen some $ω$ bindings to be
  linear, and to drop unnecessary $ω$ bindings. Array pointers are
  substituted with their value. With the additional
  requirement\improvement{Make precise}{} that |MArray| pointers are
  substituted \emph{exactly once} in $(Γ',e)$, and, when susbtituting
  in $Γ'$, only inside the body of variables with multiplicity $1$,
  and, when substituting the body of a $let$-binding, either in $Γ'$
  or in $e$, the $let$ binding must have multiplicity $1$. If
  there are |MArray| pointers in $Γ$, we additionally require that $ρ=1$.
\end{definition}

\begin{lemma}[Safety]\label{lem:actual_type_safety}
  The denotaion assignment relation defines a simulation of the
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
By induction, using the restrictions on substituting |MArray| pointers
for the \emph{shared variable} and \emph{let} rules.

\begin{theorem}[Progress]
  For any partial derivation of $Ξ ⊢ (Γ'||e ⇓ ?) :_ρ A,Σ$ or of $Γ:e⇓?$, the
  derivation can be extended.
\end{theorem}
\begin{proof}
  By liveness (\fref{lem:liveness}) it is sufficient to prove the case
  of the denotational semantics.

  Let us also note that if we erase all multiplicity from the
  denotational semantics, then we get a completely standard semantics
  for simply typed $λ$-calculus, in which progress is known to
  hold. So we it suffices to show that multiplicity annotations do not prevent the
  head of the partial derivation to match a rule.

  For instance, we need to check that the head of the partial
  derivation is not $Ξ⊢(Γ,x:_1 B = e||x ⇓ ?) :_ω A,Σ$ or
  $Ξ⊢Γ||\varid{write}~x~i~a :_ω \varid{MArray}~a, Σ$, which match no rule because
  of their multiplicities.
  \begin{itemize}
  \item $Ξ⊢Γ,x:_1 B = e||x :_ω A,Σ$ is not a well-typed state because
    it reduces to $x:_1B = x:_{ωp} B$ for some $p$, which never
    holds. By type preservation (\fref{lem:type-safety}),  $Ξ⊢Γ,x:_1 B
    = e||x :_ω A,Σ$ cannot be the head of a partial derivation.
  \item The case of $Ξ⊢Γ||\varid{write}~x~i~a :_ω \varid{MArray}~a, Σ$
    is similar, if a little more subtle. For it to be well-typed, we
    need that $Γ$ contains a binding $x :_ω \varid{MArray}~a$. We need
    the following intermediate lemmas:
    \begin{itemize}
    \item If $Ξ⊢Γ,x:_1A = e_x||u :_p B,Σ$ is the head of a partial proof, then
      $p=1$ (by type preservation)
    \item If $Ξ⊢Γ,x:_1A = e_x||u :_1 B,Σ$ is the head of a partial
      proof, then none of the $y:_ωC=e_y$ are such that $x$ is a free
      variable of $e_y$ (by type preservation).
    \item If $Ξ⊢Γ||u :_p A, Σ$ is the head of a partial proof, and
      contains an $x :_q \varid{MArray}~a$ binding, then $q=1$ (which,
      by the above lemma implies that $p=1$). This is proved by
      induction in the partial derivation, noting that the only rule
      which could introduce such a binding with $q=ω$ is the $\flet$
      rule either because the binding has multiplicity $ω$ or because
      $p=ω$\unsure{This property is not true in presence of recursive
        definition. And in fact, I can trigger the write rule in an ω
        environment using |undefined| for the |MArray|. So I'm
        guessing I should relax this rule to take arbitrary
        multiplicity. It seems that the bisimulation is left
        unchanged. It would simplify progress, because then, we would
        only have the linear variable rule to deal with.}
    \end{itemize}

  \end{itemize}

\end{proof}

\end{document}

% safety proves that the mutable semantics is equivalent to a pure
% semantics.
% liveness proves that the primitives don't block on typestate (\emph{e.g.} in the
% write primitive, we are never given an |Array|) (because typing is
% preserved in the denotational semantics, hence the denotational
% semantics can't block on a typestate).

%  LocalWords:  sequentialised supremum bisimilar observationally
%  LocalWords:  typestates denotational
