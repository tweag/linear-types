% -*- latex -*-

%% For double-blind review submission
% \documentclass[acmsmall,10pt,review,anonymous]{acmart}\settopmatter{printfolios=true}
%% For single-blind review submission
\documentclass[acmsmall,10pt,review]{acmart}\settopmatter{printfolios=true}
%% For final camera-ready submission
%\documentclass[acmsmall10pt,]{acmart}\settopmatter{}

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

\subsection{Type states}

Imagine you want to write some function in destination-passing
style~\cite[Section 3.2]{larus_destination_1998}. Destination-passing
is a standard trick, for instance in C-programming, where the caller
of a function is responsible for allocating memory for the function,
rather than the function itself. That is, instead of
\begin{code}
  f :: A -> B
\end{code}
you would write something like
\begin{code}
  fDest :: A -> Dest B -> ()
\end{code}
A ``destination'' is taken as an argument and |fDest| returns to this
destination instead of creating a new memory cell to hold a |B| as |f|
does.

Destination-passing is useful to reduce the memory footprint of
programs, and also makes programs more parallalisable, which was the
motivation of \citeauthor{larus_destination_1998}.

Let us think how you could do that in Haskell. Clearly, the above type
is wrong, as |fDest| must be doing some kind of effect as the |B|
becomes available somewhere, but Haskell's function are pure, and that
would be forbidden. You could write |fDest| in |IO|, but it would limit
its expressive power a bunch. In particular you would not be able to
express |f| in terms of |fDest|, at least not without making |f| an
|IO| action, which would expose what should otherwise be seen as an
implementation detail. Instead, let us try the |ST| monad, so that
|fDest| would look like\improvement{Link to some resource about the
  |ST| monad}
\begin{code}
  fDest :: A -> Dest s B -> ST s ()
\end{code}

To be able to write |f| in terms of |fDest|, you need to, first,
allocate some space to hold a value of type |B|, then, when it has
been filled by |fDest| return the |B| thus obtained. Since |B|
represent an immutable value and |Dest s B| represent a mutable value,
it is not safe that the same object is represented both as a |B| and a
|Dest s B| at the same time.

You must, therefore, make sure that the |Dest s b| destination is
unaccessible by the time you return a |B| value. You can use a
function such as the following:
\begin{code}
  initB :: (forall s. ST s Dest s B) -> B
\end{code}
The universal quantification ensures that the destination does not
escape the scope of the this |ST| computation. The |initB| function is
similar to the |create| function of Haskell's Vector
library\improvement{A citation for vector.}.

You can, then, give yourself a function to create a |Dest|
\begin{code}
  allocB :: ST s Dest s B
\end{code}
and you write |f|
\begin{code}
  f :: A -> B
  f a = initB $ do
    dest <- allocB
    fDest dest
    dest
\end{code} % $ -- works around a limitation in syntax highlighting

So far so good. Except that… what happens if one writes the following
program?
\begin{code}
  bad :: B
  bad = initB allocB
\end{code}
We get an uninitialised value of type |B|! And a very quick segfault!
The immediate solution to that is to make |allocB| take a default
value. But such a value is not necessarily available. And doing a
preallocation like this may create spurious additional allocation,
just what you are trying to avoid!

Back to the drawing bord: you need some kind of state, tracked in the
type, indicating whether the destination has been initialised or
not. In Haskell, this can be done using an indexed
monad\improvement{citation for indexed monads}. The destination
becomes part of the internal state of the monad:
\begin{code}
  type DestST b b' a
  return :: Dest b b a
  (>>=) :: Dest b1 b2 a -> (a -> Dest b2 b3 c) -> Dest b1 b3 c

  initB :: Dest B () () -> B
  fDest :: A -> Dest B () ()
\end{code}
Problem solved? Well… How will you write |fDest|? Surely if you have a
value of type |B|, you can fill the destination:
\begin{code}
  fill :: b -> Dest b ()
\end{code}
But using only |fill| would defeat the purpose of |fDest| entirely: you
would be defining |fDest| in terms of |f|. So you need functions to
instantiate part of a structure, creating new destinations. For
instance, if |B| is a type of pairs you want to allocate the space for
the two component and return the two destinations. Oh! It means you
must have several destination in our |Dest| monad. You can use
Haskell's type-level lists:
\begin{code}
  pairDest :: Dest ((a,b):d) (a:b:d)
\end{code}
This quickly becomes very tiresome. And you have probably lost every
chance at parallelism along the way.

With linear type, however, the story becomes much simpler: a linear
destination must be consumed exactly once, therefore we can make sure
that our |B| is properly initialised simpley by making all
destinations linear. A similar idea has been explored by
\citet{minamide_hole_1998}.
\begin{code}
  type Dest b
  fill :: b ⊸ Dest b ⊸ ()

  initB :: (Dest B ⊸ Unrestricted x) ⊸ Unrestricted (B, x)

  pairDest  :: Dest (a,b) ⊸ (Dest a, Dest b)
\end{code}
There are two things of noticed. First in the type of |initB|: the
argument of |initB| is a function which takes a linear argument of
type |Dest B| and returned an |Unrestricted x|. The |Unrestricted|
ensures that there are no linear variables left in |x|, so that the
destination cannot escape this scope. This is because anything
pointing to a linear value is itself linear and cannot be put inside
an |Unrestricted|. The other thing of notice is the type of
|pairDest|: it returns a pair of destinations. This is the ordinary
Haskell pair, but the type system ensures that it is linear: it must
be consumed exactly once, in other word both returned destinations
must be consumed exactly once.

By means of illustration, let us extend the destination \textsc{api}
with binary trees:
\begin{code}
  data Tree a = Node (Tree a) (Tree a) | Leaf a
  initTree :: (Dest (Tree a) ⊸ Unrestricted x) ⊸ Unrestricted (Tree a, x)
  leafDest :: a ⊸ Dest (Tree a) ⊸ ()
  nodeDest :: Dest (Tree a) ⊸ (Dest (Tree a), Dest (Tree a))
\end{code}
Let us proceed to write a tail-recursive map function over these trees:
\begin{code}
  mapTree :: (a⊸b) -> Tree a ⊸ Tree b
  mapTree f tree = case initTree (\d -> go [(tree, d)]) of Unrestricted (res,()) -> res
    where
      go :: [(Tree a, Dest (Tree b))] ⊸ Unrestricted ()
      go [] = Unrestricted ()
      go ((Leaf a, dest):k) = case leafDest a dest of () -> go k
      go (Tree l r, dest):k) =
        case nodeDest dest of
          (dl, dr) -> go ((l,dl):(r,dr):k)
\end{code}

This is actually quite an interesting function as the recursive |go|
loops over a list of destinations. This is an ordinary Haskell list,
but because it contains linear data it must itself be consumed exactly
once. This ensure that, despite the fact that there are an arbitrary,
statically unknown, number of |Dest (Tree a)| at any given point of
the loop, all of these desination will be filled exactly once.

\subsection{I/O protocols}

In the previous section, we got rid of the |ST| monad
entirely. Instead linear values must be threaded explicitly. This is
not really a cost in our example, as we would have to thread
destinations one way or another. However there is a gain: actions on
distinct destinations are not sequentialised. This means that the
compiler is free to reorder such actions in order to find more
optimisation opportunities.

On the other hand, in other cases, we may need actions to be fully
sequentialised, because they are interacting with the real world. This
is the world of |IO| action. In this case, linearity will not serve to
make the program less sequentialised~---~it must not be~---~but will
help make sure that a sequence of action obey a certain discipline. We
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
