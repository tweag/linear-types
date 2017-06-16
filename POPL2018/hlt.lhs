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
  Linear and affine type systems have a long and storied history, but not a
  clear path forward to integrate with existing languages such as
  Ocaml or Haskell.
  In this paper, we introduce and study a linear type system designed with two
  crucial properties in mind:
  backwards-compatibility and code reuse across linear and non-linear users of
  a library. Only then can the benefits of linear types permeate
  conventional functional programming.
  Rather than bifurcate data types into linear and non-linear
  counterparts, we instead attach linearity to {\em binders}.  Linear function
  types can receive inputs from linearly-bound values, but can also operate over
  unrestricted, regular values.

  Linear types are an enabling tool for safe and resource efficient
  systems programming. We explore the power of linear types with
  a case study of a large, in-memory data structure that must serve
  responses with low latency.
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

\section{A taste of \HaskeLL{}}
\label{sec:programming-intro}

\subsection{Freezing arrays}
\label{sec:freezing-arrays}

\subsubsection{Mutable arrays}

Let us consider immutable arrays. It is quite clear how to write an
\textsc{api} for consuming such arrays: we can retrieve the value at a
given index, map a function, pair-up values of two different arrays of
the same length, etc… But all of these combinators assume that an
array already exists. How can we create a brand new array? In the
Haskell ecosystem, the preferred solution is usually to create a
mutable array, let the programmer fill it the way he wants, and
eventually ``freeze'' the mutable array into a mutable
array.\improvement{cite vector library}\improvement{Maybe explain that
  we need the |a| argument to |newMArray| in order to initialise the
  array}
\begin{code}
  type MArray s a
  type Array a

  newMArray :: Int -> a -> ST s (MArray s a)
  write :: MArray s a -> Int -> a -> ST s ()
  read :: MArray s a -> Int -> ST s a
  unsafeFreeze :: MArray s a -> ST s (Array a)
  index :: Array a -> Int -> a
\end{code}

The freezing primitive is called |unsafeFreeze| because it
is, indeed, unsafe: after calling |unsafeArray marray| we get a new
immutable array |array|, but in order to avoid an unnecessary copy,
|array| and |marray| are actually \emph{the same array}. But any
mutation to |marray| will break the immutability of |array|. As a
consequence it is required of the caller of |unsafeFreeze| that he
will not use |marray| again after that. But this is not enforced by
the type system. Wouldn't it be better if we could tell the type
system that |marray| ought to be \emph{consumed} by the |unsafeFreeze|
call so that |marray| is not accessible to the programmer when |array|
is? This way |unsafeFreeze| would not be unsafe anymore.

\HaskeLL{} introduces a new kind of function type: the \emph{linear
  arrow} |a⊸b|. A linear function |f :: a⊸b| must consume its argument
\emph{exactly once}. This new arrow makes it possible to express the
array \textsc{api} as follows:
\begin{code}
  type MArray a
  type Array a

  newMArray :: Int -> a -> (MArray a ⊸ Unrestricted b) ⊸ Unrestricted b
  write :: MArray a ⊸ Int -> a -> MArray a
  read :: MArray a ⊸ Int -> (MArray a, Unrestricted a)
  freeze :: MArray a ⊸ Unrestricted (Array a)
  index :: Array a -> Int -> a
\end{code}
There are a few things to remark. First, and foremost, |freeze| is not
|unsafe| any more. The second thing is that |write| and |Read| consume
the |MArray|, then return the |MArray| again: this is necessary as if
we were allowed to use the same |MArray| in several places, then it
would not be possible to prevent its use after |freeze| has been
effected. It means that we have to thread the |MArray| throughout the
computation, on the other hand, none of the functions use the |ST|
monad anymore. Notice that |read| also returns an |Unrestricted a|:
you should read it as ``despite |read| being a linear function, the
|a| need not be used in a linear''.

The last thing of notice is the funny type of
|newMArray|. Specifically it does not return an array, but it asks for
a function |k| that consumes an array. The reason is that the type
system of \HaskeLL{} can express that |k| consumes its argument
exactly once. But it does not provide a direct way to return a value
which must be consumed exactly once. Also note that |k| must return an
unrestricted result, this is a common pattern in \HaskeLL{}: this make
sure that the |MArray| argument has been consumed prior to |k|
returning. If the |MArray| argument leaked, either by being directly
returned, or hidden in a closure, then its linearity would be
compromised and the \textsc{api} would be unsafe.\improvement{These
  two last paragraphs are not very tight. Improve prose. In
  particular, I don't even mention that freeze returns an
  |Unrestricted| array.}

We replaced the |ST| monad by manually threading individual mutable
arrays. The single-threadedness of each array is ensured by the type
system. Compared to |ST|, it is interesting that actions on
two independent arrays are \emph{not} sequentialised. Yielding more
opportunities for the compiler to reorder and optimise a
program.\improvement{Maybe more about the comparison to |ST|
  here. Though it would probably be better to have a dedicated section
  in the related work section.}

\subsubsection{Initialisation of byte-arrays}

Emboldened by our success, we may try to do something which is, in
regular Haskell, even more unsafe. Something that used improperly
would yield the dreaded \verb+segfault+. Indeed, |newMArray|
initialises all of its cells with some initial value. It is needed for
three reasons: we can read the mutable array, if we would access
uninitialised memory cells the program would \verb+segfault+; even if
we refrain from reading from the mutable array, we will read from the
frozen array, so it must be fully initialised; and the garbage
collector will traverse the array and cannot handle uninitialised
memory.

But if we are considering an array a binary data, \emph{i.e.} which
contains no pointer to garbage collected objects, like a |ByteArray|
in Haskell, then we know that the garbage collector will not traverse
the array. Therefore, as long as we don't access uninitialised data, a
pre-initialisation of the entire array is a waste.

With linear types, we can make sure that uninitialised data is never
accessed. There is more than one way to approach this problem. Let us
focus on the cache-friendly left-to-right initialisation: that is, we
will start with an uninitialised byte-array and fill the leftmost
byte, when we are finished, we will freeze the byte-array leaving any
remaining data uninitialised, but also inaccessible.\improvement{Say
  that |WByteArray| is write-only}
\begin{code}
  type WByteArray
  type ByteArray

  allocByteArray :: Int -> (WByteArray ⊸ Unrestricted b) ⊸ Unrestricted b
  writeByte :: World8 -> WByteArray ⊸ ()
  freezeByteArray :: WByteArray ⊸ Unrestricted ByteArray
  index :: ByteArray -> Worl8 -> a
\end{code}

\subsection{I/O protocols}

In the previous section, we got rid of the |ST| monad entirely. There
is a gain: actions on distinct arrays are not
sequentialised. This means that the compiler is free to reorder such
actions in order to find more optimisation opportunities.

On the other hand, in other cases, we need actions to be fully
sequentialised, because they are interacting with the real world. This
is the world of |IO| action. In this case, linearity will not serve to
make the program less sequentialised~---~it must not be~---~but will
help make sure that a sequence of actions obey a certain discipline. We
think of such disciplines as protocols\footnote{Such protocol can be
  imposed on actual network communications, in which case they are
  actual communication protocols. See
  \citet{wadler_propositions_2012,parente_logical_2015}, for a formal
  treatment of such communication protocols.}.

A common example of such protocol is network- or storage-based
collection. For example databases: the common feature is that getting
(or setting) an element of this collection requires I/O, hence, in
Haskell, happens in the |IO| monad.

For the purpose of this example, let us view files as collections of
lines. So that we have:
\begin{code}
  type File a

  openFile :: FilePath -> IO (File ByteString)
  readLine :: File a -> IO a
  closeFile :: File a -> IO ()
\end{code}
In this \textsc{api} we see |File a| as a cursor in a file. Each call
to |readLine| returns an |a| (the line) and moves the cursor one line
forward.

We will want that |File| behaves as much as possible as an ordinary
collection. In particular we would like to |File| to be a functor:
this is how we will parse lines.
\begin{code}
  mapFile :: (a->b) -> File a -> File b
\end{code}
We may also want ways to compose |File|s. For instance a way to zip to
files:
\begin{code}
  zipFile :: File a -> File b -> File (a,b)
\end{code}
Such a programing idiom can be found in the
\texttt{streaming}~\cite{thompson_streaming_2015} library.

The problem is that it makes a number of unintended things
possible. We have observed such mistakes in our own code in industrial
projects, and it proved quite costly to hunt down.
\begin{code}
  bad1 path = do
    file <- openFile path
    let coll = map someParsingFun file
    string <- readLine file
    value <- readLine coll
    closeFile coll

  bad2 path = do
    file <- openFile path
    let coll = map someParsingFun file
    closeFile file
    value <- readLine coll
    closeFile coll

  bad3 path1 path2 = do
    file1 <- openFile path
    file2 <- openFile path
    coll <- zipFile file1 file2
    string <- readLine file1
    value <- readLine coll
    closeFile coll

  bad4 path1 path2 = do
    file1 <- openFile path
    file2 <- openFile path
    coll <- zipFile file1 file2
    closeFile file1
    closeFile coll

\end{code}
In |bad1|, the process reads from both handlers to the same file,
reads from |file| will cause the cursor in |line| to progress. The
matter gets worse in |bad3| where the |file1| and |file2| are supposed
to be read in lockstep, but they get desynchronised by the call to
|readLine file1|. In |bad2|, |file1| is closed before |coll| is read,
and in |bad4|, |file1| is closed twice, once directly, and a second
time via |closeFile coll|.

The issue is that the intention behind |mapFile| and |zipFile| is that
the handle is transformed, not shared. It is a crucial difference with
immutable collections which can be shared freely.

Before we can apply linear types to the problem, we need to generalise
|IO| to be able to return both linear and non-linear values. To that
effect, we will make |IO| multiplicity polymorhic:
\begin{code}
  type IO p a
  return  :: a -> _ p IO p a
  (>>=)   :: IO p a ⊸ (a -> _ p IO q b) ⊸ IO q b
\end{code}
We will continue using the |do| notation even though |return| and
|(>>=)| are not quite the right type to form a monad.

The following \textsc{api} for |File| makes all the examples above
ill-typed, ensuring that we don't use the same handle under two
different guises at the same time. It ensures, in particular, that
every file is closed exactly once.
\begin{code}
  type File a

  openFile :: FilePath -> IO 1 (File ByteString)
  readLine :: File a ⊸ IO 1 (Unrestricted a, File a)
  closeFile :: File a -> IO ω ()
  mapFile :: (a->b) -> File a ⊸ File b
  zipFile :: File a ⊸ File b ⊸ File (a,b)
\end{code}

There is a price to pay in that we have to thread files at every use,
even for |readLine|. Note, however, that the \texttt{streaming}
library's \textsc{api} shares this characteristic, despite not using
linear types. What we gain for this price is a guarantee that files
will be closed exactly once and that we are not using two versions of
a file.\unsure{If we talk about borrowing, we can even alleviate that
  cost by having |readLine :: File a -> _ β IO ω a|.}

Sometimes, however, you may want to have two versions of the same
file. There are two possible semantics: any-cast~---~the two versions of
the file read from the same cursor, and each line is read by only
one of the two versions~---~and multi-cast where lines are read by
both versions. Thanks to linear types you must specify when you want
to versions of a file, at which point you can choose between any-cast
and multi-cast.
\begin{code}
  dupFileAny    :: File a ⊸ (File a, File a)
  dupFileMulti  :: File a ⊸ (File a, File a)
\end{code}

We have willfully ignored, so far, the fact that files are finite, and
that |readLine| may reach the end of the file. The real type of
|readLine| should be:
\begin{code}
  readLine :: File a ⊸ IO 1 (Maybe (Unrestricted a, File a))
\end{code}
Which is like pattern matching a list, except in |IO|. Note that if
we reach the end of the file, no new |File a| is returned, which means
that |readLine| will close the file handle in that case. So
|closeFile| only needs to be called when we do not want to consume the
entire file.

\subsection{Operational intuitions}
\label{sec:consumed}

We have said repeatedly spoken loosely of \emph{``consuming a value
  exactly once''}. But what does ``consuming a value exactly once''
mean? Let us give a more precise operational intuition:
\begin{itemize}
\item To consume exactly once a value of an atomic base type, like |Int| or |Ptr|, just evaluate it.
\item To consume a function exactly once, call it, and consume its result exactly once.
\item To consume a pair exactly once, evaluate it and consume each of its components exactly once.
\item More generally, to consume exactly once a value of an algebraic data type, evaluate
  it and consume all its linear components exactly once.
\end{itemize}

We can now give a more precise definition of what a linear function |f
:: a ⊸ b| means: |f| guarantees that \emph{if |f u| is consumed
  exactly once}, then |u| is consumed exactly once. A salient point of
this definition is that ``linear'' emphatically does not imply
``strict''. Our linear function space behaves as Haskell programmers
expect.

A consequence of this definition is that an \emph{unrestricted} value,
\emph{i.e.} one which is not guaranteed to be used exactly once, such
as the argument of a regular function |g :: a -> b|, can freely be
passed to |f|: |f| offers stronger guarantees than regular
functions. On the other hand a linear value |u|, such as the argument of
|f|, \emph{cannot} be passed to |g|: consuming |g u| may consume |u| several
times, or none at all, both violating the linearity guarantee that |u|
must be consumed exactly once.

In light of this definition, suppose that we have |f :: a ⊸ b| and |g
:: b -> c|. Is |g (f x)| correct? The answer depends on the linearity
of |x|:
\begin{itemize}
\item If |x| is a linear variable, \emph{i.e.} it must be consumed
  exactly once, we can ensure that it's consumed exactly once by
  consuming |f| exactly once: it is the definition of linear
  functions. However, |g| does not guarantee that it will consume |f
  x| exactly once, irrespective of how |g (f x)| is consumed. So |g (f
  x)| cannot be well-typed.
\item If |x| is an unrestricted variable, on the other hand, there is
  no constraint on how |x| must be consumed. So |g (f x)| is perfectly
  valid. And it is, indeed, well-typed. Refer to \fref{sec:statics}
  for the details.
\end{itemize}

In the same spirit, an unrestricted value |u| can never point to a
linear value |v|: if |u| is never consumed (which is a correct use of
an unrestricted value), then |v| will never be consumed either, which
is incorrect of a linear value.

\subsection{Linear data types}
\label{sec:linear-constructors}

Using the new linear arrow, we can (re-)define Haskell's list type as follows:
\begin{code}
data [a] where
  []   :: [a]
  (:)  :: a ⊸ [a] ⊸ [a]
\end{code}
That is, we give a linear type to the |(:)| data constructor.
Crucially, this is not a new, linear list type: this \emph{is}
\HaskeLL{}'s list type, and all existing Haskell functions will work
over it perfectly well.  But we can \emph{also} use the very same list
type to contain linear values (such as file handles) without
compromising safety; the type system ensures that resources in a list
will eventually be consumed by the programmer, and that they will not
be used after that.

Let us introduce a piece of terminology: variables can be either
linear or unrestricted depending on what kind of function introduced
them, we call this dichotomy the \emph{multiplicity} of the
variable. Furthermore we say that linear variables have multiplicity
$1$ and unrestricted variables have multiplicity $ω$.

Many list-based functions preserve the multiplicity of data, and thus
can be given a more precise type. For example we can write |(++)| as
follows:
\begin{code}
(++) :: [a] ⊸ [a] ⊸ [a]
[]      ++ ys = ys
(x:xs)  ++ ys = x : (xs ++ ys)
\end{code}
The type of |(++)| tells us that if we have a list |xs| with
multiplicity $1$, appending any other list to it will never duplicate
any of the elements in |xs|, nor drop any element in
|xs|\footnote{This follows from parametricity.  In order to {\em free}
  linear list elements, we must pattern match on them to consume them,
  and thus must know their type (or have a type class instance).
  Likewise to copy them.}.

Giving a more precise type to |(++)| only {\em strengthens} the
contract that |(++)| offers to its callers; \emph{it does not restrict
  its usage}. For example:
\begin{code}
  sum :: [Int] ⊸ Int
  f :: [Int] ⊸ [Int] -> Int
  f xs ys = sum (xs ++ ys) + sum ys
\end{code}
Here the two arguments to |(++)| have different multiplicities, but
the function |f| guarantees that it will consume |xs| exactly once if
|f xs ys| is consumed exactly once.

For an existing language, being able to strengthen |(++)|, and similar
functions, in a {\em backwards-compatible} way is a huge boon.  Of
course, not all functions are linear: a function may legitimately
demand unrestricted input.  For example, the function |f| above
consumed |ys| twice, and so |ys| must have multiplicity $\omega$, and
|f| needs an unrestricted arrow for that argument.

Generalising from lists to arbitrary algebraic data types, we designed
\HaskeLL{} so that when in a traditional Haskell (non-linear) calling
context, linear constructors degrade to regular Haskell data
types. Thus our radical position is that data types in \HaskeLL{}
should have {\em linear fields by default}, including all standard
definitions, such as pairs, tuples, |Maybe|, lists, and so on.  More
precisely, when defined in old-style Haskell-98 syntax, all fields are
linear; when defined using GADT syntax, the programmer can explicitly
choose.  For example, in our system, pairs defined as
\begin{code}
data (,) a b = (,) a b
\end{code}
would use linear arrows. This becomes explicit when defined in GADT syntax:
\begin{code}
data (a,b) where  (,) ::  a ⊸ b ⊸ (a,b)
\end{code}
We will see in \fref{sec:non-linear-constructors} when it is also
useful to have contstructors with unrestricted arrows.

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
  Thus, \HaskeLL{} features quantification over multiplicities and
  parameterised arrows (|A → _ q B|).  Using these, |map| can be given
  the following most general type: |∀ρ. (a -> _ ρ b) -> [a] -> _ ρ
  [b]|.
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

\subsection{Linearity of constructors: the usefulness of unrestricted constructors}
\label{sec:non-linear-constructors}

We saw in \fref{sec:linear-constructors} that data types in \HaskeLL{} have
linear arguments by default. Do we ever need data constructors
unrestricted arguments?  Yes, we do.

Using the type |T| of \fref{sec:consumed}, consider the |freeze|
function from \fref{sec:freezing-arrays}. We could define it in
\textsc{cps} style but a direct style is more convenient: %
\begin{code}
  freeze :: (Array a -> r) ⊸ MArray a ⊸ r mediumSpace vs. mediumSpace copy :: MArray a ⊸ Unrestricted (Array a)
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
With our primitive in hand, we can now use ordinary code to freeze
a list of |Marray| values into a list of arrays (we mark patterns in
|let| and |where|
with |!|, Haskell's syntax for strict pattern bindings: \HaskeLL{}
does not support lazy pattern bindings of linear values, |case| on the
other hand, is always strict):
\begin{code}
  freezeList :: [MArray a] ⊸ Unrestricted [Array a]
  freezeList (x:xs) = Unrestricted (x':xs')  where  !(Unrestricted xs')  = freezeList xs
                                                    !(Unrestricted x')   = freeze x
\end{code}

Note that according to the definition of \fref{sec:consumed},
consuming a value of type |Unrestricted a| means evaluating it, the
|a| inside need not be consumed, or can be consumed any number of
time. Therefore a function of type |a ⊸ Unrestricted b| is a function
that will consume its argument exactly once if its result is ever
evaluated. This is why |Unrestricted| appears in many abstractions in
order to ensure that values have been consumed at a given point in the
program.

\section{\calc{}: a core calculus for \HaskeLL}
\label{sec:statics}

In this section we turn to the calculus at the core of \HaskeLL{},
which we refer to as
\calc{}, and for which we provide a step-by-step account of its syntax and typing
rules.

As we discussed in \fref{sec:consumed}, the meaning of linear
functions is that they will consume their argument \emph{exactly once}
if their result is consumed exactly once. The role of the type system
of \calc{} is to enforce this very property.

Let us point out that closures (partial applications or lazy thunks)
may need to be consumed exactly once. Indeed, as we explained in
\fref{sec:consumed}, unrestricted values do not point to linear
values, so if any member of a closure is linear, so must the closure
itself.

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
that consuming $f u : B$ exactly once will consume $q$ times the value
$u{:}A$. Therefore, a function of type $A→B$ \emph{must} be applied to
an unrestricted argument, while a function of type $A⊸B$ \emph{may} be
applied to any argument, linear or not.
%
One might, thus, expect the type $A⊸B$ to be a subtype of $A→B$. This
is however, not so, because there is no notion of subtyping in \calc{}. This
is a salient choice in our design. Our objective is to integrate with
existing typed functional languages such as Haskell and the
\textsc{ml} family, which are based on Hindley-Milner-style
polymorphism. Hindley-Milner-style polymorphism, however, does not
mesh well with subtyping as the extensive exposition by
\citet{pottier_subtyping_1998} witnesses.  Therefore \calc{} uses
multiplicity polymorphism for the purpose of reuse of higher-order
function as we described in \fref{sec:lin-poly}.

Data type declarations (see \fref{fig:syntax}) are of the following form:
\begin{align*}
  \data D  \mathsf{where} \left(c_k : A₁ →_{q₁} ⋯    A_{n_k} →_{q_{n_k}} D\right)^m_{k=1}
\end{align*}
The above declaration means that \(D\) has \(m\) constructors \(c_k\)
(where \(k ∈ 1…m\)), each with \(n_k\) arguments. Arguments of
constructors have a multiplicity, just like arguments of functions: an
argument of multiplicity $ω$ means that the data type can store, at
that position, data which \emph{must} reside in the dynamic heap;
while a multiplicity of $1$ means that data at that position
\emph{can} reside in either heap. For simplicity's sake, we assume
that the multiplicities $q_i$ must be concrete (\emph{i.e.} either $1$
or $ω$) even though \HaskeLL{} has multiplicity-polymorphic data
types.

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
of the multiplicity annotations on abstractions and arrows.

For multiplicities we need the concrete multiplicities $1$ and $ω$ as
well as multiplicity variables (ranged over by the metasyntactic
variables \(π\) and \(ρ\)) for the sake of polymorphism. However, we
are going to need to multiply and add multiplicities together,
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
to consume said value exactly once.

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
is the design choice which makes it possible to consider data-type
constructors as linear by default, while preserving the semantics of
the intuitionistic $λ$-calculus (as we already stated in
\fref{sec:linear-constructors}). For \HaskeLL{}, it means that types
defined in libraries which are not aware of linear type (\emph{i.e.}
libraries in pure Haskell) can nevertheless be immediately useful in a
linear context. Inheritance of multiplicity is thus crucial for
backwards compatibility, which is a design goal of
\HaskeLL{}.\improvement{Announce here what it means in terms of linear
logic maybe?}

\section{Evaluation}
\label{sec:evaluation}

\section{Implementing \HaskeLL}
\label{sec:implementation}

\begin{itemize}
\item monomorphic multiplicity only
\item only modifies the type inference mechanism
\item modify the type of arrow to accept multiplicity
\item arrow type used a lot in \textsc{ghc}, therefore quite a bit of
  menial tasks
\item Types are input, multiplicities are output
\item Lattice-ordered semi-ring
\item diff currently affects 1122, adds 436 net lines
\item 3 files account for almost half of the changes: a file dedicated
  to multiplicity operations, the file responsible of type
  environment, and the file responsible for type-checking patterns.
\item smaller changes all over the type-checker (113 files changed)
\item Not compatible with all \textsc{ghc} syntax extensions.
\end{itemize}
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
% \item |ST|-like regions confine to a stack-like allocation discipline.
%   Scopes cannot intersect arbitrarily, limiting the applicability of
%   this technique.
\item |ST| actions cannot be interleaved with |IO| actions. So in our
  mutable array examples, for instance, it is not possible to provide
  a safe abstraction around |unsafeFreeze :: MArray s a -> ST s (Array
  a)| which will also make it possible to use |IO| actions to fill in
  the array.
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
\fref{sec:fusion}.\unsure{The discussion on fusion may well disappear}

Because of this weak duality, we perhaps could as well have
retrofitted uniqueness types to Haskell. But several points
guided our choice of designing \HaskeLL{} around linear
logic rather than uniqueness types: (a) functional languages have more use
for fusion than in-place update (if the fact that \textsc{ghc} has a cardinality
analysis but no non-aliasing analysis is any indication); (b) there is a
wealth of literature detailing the applications of linear
logic — see \fref{sec:applications}; (c) and decisively, linear type systems are
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
uses kinds to separate affine from unrestricted arguments.

It is a case in point for kind-based systems being more complex: for
the sake polymorphism, Alms deploys an elaborate dependent kind
system. Even if such a kind system could be added to an existing
language implementation, Alms does not attempt to be backwards
compatible with an \textsc{ml} dialect.

\subsection{Ownership typing à la Rust}

Rust \cite{matsakis_rust_2014} features ownership (aka uniqueness)
types. But like the original formulation of linear logic, in Rust \verb+A+
stands for linear values, unrestricted values at type \verb+A+ are denoted
\verb+RC<A>+, and duplication is explicit.

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
to latency-sensitive and resource starved programs is still
possible.\improvement{Change depending on what we put in the
  evaluation section}

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

\improvement{Not the right place, but let us not forget to cite the
  very relevant: \cite{pottier_programming_2013}}
\unsure{This section will need a clean up, to be more in phase of what
we present in the evaluation section}

\Citet{wakeling_linearity_1991} produced a complete implementation of
a language with linear types, with the goal of improving the
performance. Their implementation features a separate linear heap, as
\fref{sec:dynamics} where they allocate as much as possible in the
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
bidirectionality: typing contexts go in, inferred multiplicities come
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

\subsection{Fusion}
\label{sec:fusion}

\improvement{This section seems to be unclear. Either too long or too short.}
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

Linear types address this issue and serve as a programmer-facing
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

\improvement{This section could speak about the borrowing multiplicity.}
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
\section{Appendix}

Text of appendix \ldots

\end{document}

%  LocalWords:  sequentialised
