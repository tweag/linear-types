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
%include polycode.fmt
%format .         = ". "
%format forall a         = "∀" a
%format _ (a)         = "_{" a "}"
%format ω = "\omega"
%format π = "\pi"
%format ρ = "\rho"
%format ⅋ = "\parr"
%subst keyword a = "\mathsf{" a "}"
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
type to contain linear resources (such as file handles) without
compromising safety; the type system ensures that resources in a list
will eventually be deallocated by the programmer, and that they will
not be used after that.

Many list-based functions conserve the multiplicity of data, and thus can
be given a more precise type. For example we can write |(++)| as follows:
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
the function |f| guarantees that it will consume |xs| precisely once.

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

\section{\calc{}: a core calculus for \HaskeLL}
\label{sec:statics}

\section{Evaluation}
\label{sec:evaluation}

\section{Implementing \HaskeLL}
\label{sec:implementation}

\section{Related work}
\label{sec:related}

\section{Conclusion and future work}

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
