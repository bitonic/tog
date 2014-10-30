\documentclass{article}
\usepackage[square,sort,comma,numbers]{natbib}
\usepackage{amsmath}
\usepackage{semantic}
\usepackage{hyperref}
\usepackage[normalem]{ulem}
\usepackage{graphicx}
\usepackage{caption}
\usepackage{subcaption}
\usepackage{todonotes}
%include polycode.fmt

%format ^ = " "
%format ^^ = "\;"

%format Bool = "\mathsf{Bool} "
%format true = "\mathsf{true} "
%format false = "\mathsf{false} "
%format alpha = "\alpha "
%format Gamma = "\Gamma "
%format !- = "\vdash "
%format Unit = "\mathsf{Unit} "
%format Nat = "\mathsf{Nat} "
%format Pi = "\Pi "
%format Sg = "\Sigma "
%format Bot = "\bot "
%format Set = "\mathsf{Set} "
%format absurd (a) (b) = "\mathbf{absurd}" ^^ a ^^ b
%format tt = "\mathsf{tt} "
%format * = "\times "
%format fst (a) = "\mathbf{fst}" ^^ a
%format snd (a) = "\mathbf{snd}" ^^ a
%format BoolOrNat = "\mathbf{BoolOrNat} "
%format refl = "\mathsf{refl} "
%format test = "\mathbf{test} "
%format ite (x) (a) (u) (v) (t) = if t ^^ "/" x "." A then u else v
%format ~> = "\leadsto "
%format beta = "\beta "
%format nil = "\cdot "
%format valid = "\uline{\text{valid}} "
%format sub (x) (u) (t) = t "[" x := u "]"
%format := = "\mapsto "
%format (vec (a)) = "\overrightarrow{" a "}"
%format app (t) (u) = t u
%format ppa (u) (t) = t ^^ u
%format Delta = "\Delta "
%format Con = "\mathcal{C} "
%format Con_1 = "\mathcal{C}_1 "
%format Con_2 = "\mathcal{C}_2 "
%format << = "\llbracket "
%format >> = "\rrbracket "
%format Id = "\mathsf{Id} "
%format Lookup (a) = "\textsc{Lookup}(" a ")"
%format elaborate (sg) (a) (b) (c) = "\llbracket " sg "," a " \vdash " b " : " c " \rrbracket "
%format fresh = "\textbf{fresh} "
%format return = "\textbf{return} "
%format empty = "\varnothing "
%format `union` = "\cup "
%format ==> = "\Rightarrow "
%format <== = "\Leftarrow "
%format Sg_0 = "\Sigma_0 "
%format Sg_1 = "\Sigma_1 "
%format Sg_2 = "\Sigma_2 "
%format Signature = "\mathsf{Signature} "
%format Term = "\mathsf{Term} "
%format Type = "\mathsf{Type} "
%format Constraint = "\mathsf{Constraint} "
%format Context = "\mathsf{Context} "
%format t_0     = "t_0 "

%subst dummy = "\_ "

\begin{document}
\title{Type checking in the presence of meta-variables}
\author{Francesco Mazzoli}
\maketitle

\begin{abstract}
  \todo{Should I use ``pattern'' or ``higher order''?}  In this paper we
  describe how to take advantage of higher order unification in a type
  theory with meta-variables.  The literature usually presents the
  unification algorithm as a standalone component.  However the need to
  check definitional equality of terms while type checking gives rise to
  a tight interplay between type checking and unification.  We propose
  an algorithm to express type checking entirely in the form of
  unification constraints, thus making the whole process significantly
  more modular and understandable.
\end{abstract}

\section{Introduction}

Theories with dependent types have been successfully exploited to design
programming languages and theorem provers, such as Agda
\cite{norell2007}, Idris \cite{brady2013}, or Coq \cite{coqart}.  To
make these systems usable, the user is presented with a language much
richer than the underlying type theory, which will hopefully be small
enough to gain confidence in the correctness of the code that type
checks it.

One key piece in making a type theory palatable by users is the addition
of \emph{meta-variables}, standing for yet to be determined terms, and
solved by unification.  Their usage in traditional programming languages
is confined to type inference and thus they can stand in only for types.
In dependently typed languages types can contain any terms, and thus
meta-variables are usually extended to stand in for any term in our
language.  This has led to their use beyond inference, such as
interactive proof development.

The apparently simple task of integrating meta-variables in a simple
type checking algorithm for dependent types gives rise to complications.
For example, consider the task of type checking
\begin{code}
  true : if alpha <= 2 then Bool else Nat
\end{code}
Where |alpha| is an uninstantiated meta-variable of type |Nat|.  We
want the type of |true| to be |Bool|, but reduction is impeded by
|alpha|.  Thus, we cannot complete type checking until |alpha| is
instantiated, and we will have to postpone type checking until it
is.\footnote{Note that we cannot instantiate |alpha| without loss of
  generality, since both |0| and |1| are acceptable solutions.}
The key observation is that type checking dependent types involves
normalizing terms, something that can be obstructed by meta-variables.

This need to ``suspend'' and ``resume'' type checking gives rise to a
sort of concurrency that makes reasoning about the type checking
algorithm arduous.  In this paper we propose an algorithm that expresses
a type checking problem entirely in the form of unification constraints,
generated through a static traversal of the term to be type checked.  We
expand on ideas developed in Agda \cite{norell2007} and
Epigram, \todo{Add citation for Epigram}
but we simplify matters considerably by separating type checking and
unification. \todo{Maybe state advantages more clearly}

In the rest of the paper, we will explain the problem more clearly.
Then we will present the algorithm in detail using a simple type theory
as example.  Finally, we will briefly describe a unification procedure
capable of solving the generated constraints, and describe how the
algorithm can be extended to support popular language features. We have
implemented the presented algorithm in a prototype, \texttt{tog}, which
covers a subset of Agda -- every \texttt{tog} program is also a valid
Agda program.\footnote{The source code for \texttt{tog} is available at
  \url{https://github.com/bitonic/tog}.}

\section{The problem}
\label{problem}

In this section we will explain in more details the challenges faced
when type checking dependent types with meta-variables, and sketch a
solution.  An Agda-like syntax and types will be used throughout the
examples, please refer to appendix \ref{examples-syntax} for
clarifications.

Going back to the problem of type checking
\begin{code}
  true : BoolOrNat alpha
\end{code}
Given
\begin{code}
  BoolOrNat : Nat -> Set
  BoolOrNat = \ x -> if x <= 2 then Bool else Nat

  alpha : Nat
  alpha = _
\end{code}
there are various tempting ways to approach the problem.  The most
conservative approach is to stop type checking when faced with
\emph{blocked} terms (terms whose normalization is impeded by some
meta-variables).  However, this approach is unsatisfactory in many
instances.

Consider
\begin{code}
  (true, refl) : (BoolOrNat alpha * alpha == 0)
\end{code}
Type checking this pair will involve type checking |true : BoolOrNat
alpha| and then |refl : alpha == 0|. If we give up on the first type
checking problem, we will not examine the second, which will give us a
solution for |alpha| (|alpha := 0|).  After instantiating |alpha| we
can easily go back and successfully type check the first part.  In
general, we want to attempt to type check as much as possible, to
instantiate as many meta-variables as possible.

Another approach is to assume that blocked type checking problems will
eventually be solved, and continue type checking.  However, this road is
dangerous since we need to be careful not to generate ill-typed terms or
invalid type checking contexts, as noted by Norell\cite{norell2007}.
Consider
\begin{code}
  test : (alpha == 5 * ((x : BoolOrNat alpha) -> BoolOrNat (not x)) -> Nat)
  test = (refl, \ g -> g 0)
\end{code}
Type checking the definition |test| will involve checking that its type
is a valid type, and that its body is well typed.  Checking the former
will involve making sure that
\begin{code}
  BoolOrNat alpha = Bool
\end{code}
since we know that the type of |x| must be |Bool|, given that |x| is
used as an argument of |not : Bool -> Bool|.\footnote{Note that, while
  |alpha == 5| appears in the type for |test|, this does not mean
  that |alpha| will be unified with |5| when type checking the type.
  However, type checking |refl : alpha == 5| will.}

If we assume that the the type is valid, we will proceed and type check
the body pairwise.  Type checking the first element -- a proof by
reflexivity that |alpha| is equal to |5| -- will instantiate |alpha|
to |5|, and then we will be faced with
\begin{code}
  (\ g -> g 0) : ((x : Nat) -> BoolOrNat (not x)) -> Nat
\end{code}
Note that the type is ill-typed\footnote{|x|, of type |Nat|, appears as
  an argument to the boolean function |not|.}, violating the usual
invariants present when type checking.  Worse, to type check we will
instantiate |x| with |0|, ending up with |BoolOrNat (not 0)|.  With some
effort we can exploit this problem to make the type checker loop,
rendering type checking undecidable. \todo{Consider adding less
  contrived example}

As mentioned in the introduction, at the heart of the problem lies the
fact that to type check we need to weak head normalize terms.
\todo{Weak head normalize?} If reduction is impeded by meta-variables,
we cannot proceed.  To overcome this problem, McBride \todo{Add citation
  if there is one} and then Norell proposed to define type checking as
an \emph{elaboration} procedure: given the problem of type checking |t|
against |A| in context |Gamma|, type checking will produce a term |t'|
that approximates |t|:
\begin{code}
  Gamma !- t : A ~> t'
\end{code}
|t'| is an approximation of |t| in the sense that it it can be turned
into |t| by instantiating certain meta-variables -- if a subterm of |t|
cannot be type checked a placeholder meta-variable will be put in its
place.  Type checking will also consist in making sure that, once the
postponed type checking problems can be solved, the placeholder
meta-variables will be instantiated accordingly.

For instance, when type checking the type of |test|, we'll have
\begin{code}
  nil  !-  ((x : BoolOrNat alpha) -> BoolOrNat (not x)) -> Nat  ^^ :  ^^ Set
       ~>  ((x : BoolOrNat alpha) -> BoolOrNat beta)    -> Nat
\end{code}
Since we cannot type check
\begin{code}
  x : BoolOrNat alpha !- not x : Bool
\end{code}
a fresh meta-variable |beta| of type |Bool| in context |x : BoolOrNat
alpha| is placed in the place of |not x|.  Then, when checking the body
of |test|, we will check it against the approximated type generated
above.  When |alpha| is instantiated, we can resume checking that
|BoolOrNat alpha == Bool|, and if we are successful, instantiate |beta
:= not x|.  This will prevent us from running into problems when type
checking the body.

The Agda system, as described in Norell's thesis and according to the
current implementation, implements this elaboration interleaving type
checking and unification, using some fairly complicated machinery.  Our
contribution is to describe a type checking problem entirely in terms of
unification constraints, greatly simplifying the algorithm. Unification,
the most complicated part of type checking, can be completely separated
from the logic that implements the typing rules. This modularity,
amongst the other advantages, makes it very easy to experiment with
different unification ``backends'' used by the same type checking
``frontend''.

More specifically, we will elaborate a type checking problem into a well
typed term and a set unification constraints:
\begin{code}
  << Gamma !- t : A >> => (t', Con)
\end{code}
Where the |Con| is a set of heterogenous unification constraints of the
form
\begin{code}
  Gamma !- t : A = u : B
\end{code}

\section{The type theory}

\todo{Should I add |Bot| and maybe the identity type?}
\todo{Explain why we need spine syntax -- for the same reason we need it
  in bidi type checking}

To present the type checking algorithm we will make use of a simple type
theory, whose syntax is shown in figure \ref{syntax}.  While small, it
contains all the elements necessary to extend the presented ideas to a
richer language, such as one with user defined data types and records.

Most operations are done under a context (denoted by |Gamma| or
|Delta|), that stores the types of free variables; and a signature |Sg|,
that stores the type and the body (if present) of defined constants.
Their syntax is shown in figure \ref{contexts-signatures}. In our case
we use the signature exclusively to store meta-variables, but in a real
language we would use it to store arbitrary definitions. We tacitly
assume that no duplicate names are present in contexts and signatures.
Note that a signature contains only closed terms so we will not have an
explicit representation of meta-variables in a context.  Instead, when
creating a new meta-variable |alpha| of type |A| in context |Gamma|, we
will have |alpha| to abstract over |Gamma| by giving it the type |Gamma
-> A|.

The typing checking rules are shown in figure \ref{typing-rules}.
Neutral terms are represented in spine form, a necessary condition to
perform bidirectional type checking and as we will see to perform our
algorithm.  Note that while neutral terms are denoted by |h ^ (vec e)|,
where |(vec e)| is a list of eliminators, we adopt a more readable
syntax when the eliminators are known -- in their syntax $\_$ denotes
where the head will appear.  The signature |Sg| is kept implicit, since
the rules never modify it.  Every mention of |Gamma| and |Sg| is assumed
to be valid according to the rules in figure
\ref{context-signature-validity}.  Our type theory includes a universe
|Set| equipped with an inconsistent typing rule |Set : Set| for the sake
of simplicity, but our presentation can be extended with stratified
universes.\footnote{Note that a simpler theory like Martin-L{\"o}f's
  logical framework is not affected by the problems we have mentioned in
  section \ref{problem}, since we have no mean to compute
  types.}\todo{Clarify here}

As mentioned, our type checking rules are bidirectional: the type of
neutral terms is inferred, everything else is checked.  This allows us
to have untyped constructors for dependent functions and dependent
products.\todo{Add equality}

\begin{figure}
  \begin{code}
    A, B, C, t, u, v    
        ::=  Set                                          -- Type of types
        |    Bot                                          -- Empty type
        |    Unit | tt                                    -- Unit type
        |    Bool | true | false                          -- Booleans
        |    (x : A) -> B | \ x -> t                      -- Dependent functions
        |    (x : A) *  B | (t, u)                        -- Dependent products
        |    h ^ (vec e)                                  -- Neutral term

    h   ::=  x                                            -- Variables
        |    alpha                                        -- Meta-variables

    e   ::=  absurd A                                     -- |Bot| elimination
        |    ite x A t u                                  -- |Bool| elimination
        |    ppa t                                        -- Function application
        |    fst | snd                                    -- Product elimination
  \end{code}
  \caption{Terms, heads, and eliminators syntax.}
  \label{syntax}
\end{figure}

\begin{figure}
  \begin{code}
    Gamma, Delta  ::= nil | Gamma; x : A                        -- Contexts
  
    Sg            ::= nil | Sg; alpha : A | Sg; alpha : A := t  -- Signatures
  \end{code}
  \caption{Context and signature syntax.}
  \label{contexts-signatures}
\end{figure}

\begin{figure}
  \centering
  \begin{subfigure}[b]{0.4\textwidth}
    \centering
    \[
    \inference{}{|!- nil|}
    \]
    \[
    \inference{
      |!- Gamma| & |Gamma !- A : Set|
    }{
      |!- Gamma; x : A|
    }
    \]
    \caption{\boxed{|!- Gamma|}}
  \end{subfigure}%
  ~
  \begin{subfigure}[b]{0.58\textwidth}
    \[
    \inference{}{|!- nil|}\quad
    \inference{
      |!- Sg| & |Sg, nil !- A : Set|
    }{
      |!- Sg; alpha : A|
    }
    \]
    \[
    \inference{
      |!- Sg| & |Sg, nil !- A : Set| & |Sg, nil !- t : A|
    }{
      |!- Sg; alpha : A := t|
    }
    \]
    \caption{\boxed{|!- Sg|}}
  \end{subfigure}
  \caption{Context and signature validity.}
  \label{context-signature-validity}
\end{figure}

\begin{figure}
  \begin{subfigure}[b]{1\textwidth}
    \[
    \inference{}{|Gamma !- Set <== Set|}\quad
    \inference{}{|Gamma !- Bot <== Set|}\quad
    \inference{}{|Gamma !- Unit <== Set|}\quad
    \inference{}{|Gamma !- tt <== Unit|}
    \]
    \[
    \inference{}{|Gamma !- Bool <== Set|}\quad
    \inference{}{|Gamma !- true <== Bool|}\quad
    \inference{}{|Gamma !- false <== Bool|}
    \]
    \[
    \inference{|Gamma !- A <== Set| & |Gamma; x : A !- B <== Set|}{
      |Gamma !- (x : A) -> B <== Set|
    }\quad
    \inference{|Gamma; x : A !- t <== B|}{|Gamma !- \ x -> t <== (x : A) -> B|}
    \]
    \[
    \inference{|Gamma !- A <== Set| & |Gamma; x : A !- B <== Set|}{
      |Gamma !- (x : A) * B <== Set|
    }\quad
    \inference{|Gamma !- t <== A| & |Gamma !- u <== sub x t B|}{
      |Gamma !- (t, u) <== (x : A) * B|  
    }
    \]
    \[
    \inference{|Gamma !- h ^ (vec e) ==> A|}{
      |Gamma !- h ^ (vec e) <== A|
    }
    \]
    \caption{\boxed{|Sg, Gamma !- t <== A|} Terms type checking}
  \end{subfigure}

    \vspace{0.3cm}

    \begin{subfigure}[b]{1\textwidth}
      \[
      \inference{|x : A `elem` Gamma|}{
        |Gamma !- x ^^ nil ==> A|
      }\quad
      \inference{|alpha : A `elem` Sg|}{
        |Gamma !- alpha ^^ nil ==> A|
      }
      \]
      \[
      \inference{|Gamma !- h ^ (vec e) ==> Bool| & |Gamma !- A <== Set|}{
        |Gamma !- ite x A t u ((h ^ (vec e))) ==> sub x (h ^ vec e) A|
      }
      \]
      \[
      \inference{|Gamma !- h ^ (vec e) ==> Bot| & |Gamma !- A <== Set|}{
        |Gamma !- absurd A ((h ^ (vec e))) ==> A|
      }\quad
      \inference{|Gamma !- h ^ (vec e) ==> (x : A) -> B| & |Gamma !- u <== A|}{
        |Gamma !- h ^ (vec e) ^ u ==> sub x (h ^ (vec e)) B|
      }
      \]
      \[
      \inference{|Gamma !- h ^ (vec e) ==> (x : A) * B|}{
        |Gamma !- fst ((h ^ (vec e))) ==> A|
      }\quad
      \inference{|Gamma !- h ^ (vec e) ==> (x : A) * B|}{
        |Gamma !- snd ((h ^ (vec e))) ==> sub x (fst ((h ^ (vec e)))) B|
      }
      \]
      \caption{\boxed{|Sg, Gamma !- h ^ (vec e) => A|} Neutral terms type inference}
    \end{subfigure}
  \caption{Typing rules. A signature |Sg| is kept implicit throughout
    the rules, since rules never manipulate it.}
  \label{typing-rules}
\end{figure}

\section{The algorithm}

\begin{figure}
  % \[
  % \inference{}{
  %   |Gamma !- Set : A ==> alpha, Set : Set|
  % }\quad
  % \inference{}{
  %   |Gamma !- Bot : A ==> alpha, Bot : Set|
  % }
  % \]
  % \[
  % \inference{}{
  %   |Gamma !- Unit : A ==> alpha, Unit : Set|
  % }\quad
  % \inference{}{
  %   |Gamma !- tt : A ==> alpha, tt : Unit|
  % }
  % \]
  % \[
  % \inference{}{
  %   |Gamma !- Bool : A ==> alpha, Unit : Set|
  % }
  % \]
  % \[
  % \inference{}{
  %   |Gamma !- true : A ==> alpha, true : Bool|
  % }\quad
  % \inference{}{
  %   |Gamma !- false : A ==> alpha, false : Bool|
  % }
  % \]
  % \[
  % \inference{
  %   |Gamma !- A : Set ==> A', Con_1| & |Gamma; x : A' !- B : Set ==> B', Con_2|
  % }{
  %   |Gamma !- (x : A) -> B : C => alpha, 
  % }
  % \]
\end{figure}

\section{The big picture}

\section{Unification?}

\section{Bidirectional type checking}

\appendix
\section{Examples syntax}
\label{examples-syntax}

\todo{Actually write the syntax}

\bibliographystyle{abbrv}
\bibliography{type-checking-metas}

\end{document}
