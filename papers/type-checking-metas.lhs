\documentclass[a4paper,UKenglish]{lipics}
\usepackage{amsmath}
\usepackage{semantic}
\usepackage{hyperref}
\usepackage[normalem]{ulem}
\usepackage{graphicx}
\usepackage{caption}
\usepackage{todonotes}
\usepackage{microtype}

\newcommand{\mytodo}[2][]{\todo[color=gray!20,size=\scriptsize,fancyline,#1]{#2}}

%include polycode.fmt

%format ^ = " "
%format ^^ = "\;"

%format Bool = "\mathsf{Bool} "
%format true = "\mathsf{true} "
%format false = "\mathsf{false} "
%format alpha = "\alpha "
%format Gamma = "\Gamma "
%format Gamma_1 = "\Gamma_1 "
%format Gamma_2 = "\Gamma_2 "
%format Gamma_3 = "\Gamma_3 "
%format Gamma_4 = "\Gamma_3 "
%format !- = "\vdash "
%format Unit = "\mathsf{Unit} "
%format Nat = "\mathbf{Nat} "
%format Pi = "\Pi "
%format Sg = "\Sigma "
%format Sg' = "\Sigma^{‎\prime} "
%format Bot = "\bot "
%format Set = "\mathsf{Set} "
%format absurd (a) (b) = "\mathbf{absurd}" ^^ a ^^ b
%format tt = "\mathsf{tt} "
%format * = "\times "
%format fst (a) = "\mathbf{fst}" ^^ a
%format snd (a) = "\mathbf{snd}" ^^ a
%format BoolOrNat = "\mathbf{BoolOrNat} "
%format BoolOrNat' = "\mathbf{BoolOrNat} "
%format refl = "\mathsf{refl} "
%format test = "\mathbf{test} "
%format ite  (x) (a) (u) (v) (t) = if t ^^ "/" x "." a then u else v
%format ~> = "\ \leadsto\ "
%format beta = "\beta "
%format gamma = "\gamma "
%format nil = "\cdot "
%format valid = "\uline{\text{valid}} "
%format sub (x) (u) (t) = t "[" x := u "]"
%format (vec (a)) = "\overline{" a "} "
%format app (t) (u) = t u
%format ppa (u) (t) = t ^^ u
%format Delta = "\Delta "
%format Con = "\mathcal{C} "
%format Con_1 = "\mathcal{C}_1 "
%format Con_2 = "\mathcal{C}_2 "
%format Con_3 = "\mathcal{C}_3 "
%format Con_4 = "\mathcal{C}_4 "
%format << = "\llbracket "
%format >> = "\rrbracket "
%format Id = "\mathsf{Id} "
%format Lookup (a) = "\textsc{Lookup}(" a ")"
%format fresh = "\textbf{fresh} "
%format return = "\textbf{return} "
%format empty = "\varnothing "
%format `union` = "\cup "
%format ==> = "\Rightarrow "
%format <== = "\Leftarrow "
%format Sg_0 = "\Sigma_0 "
%format Sg_1 = "\Sigma_1 "
%format Sg_2 = "\Sigma_2 "
%format Sg_3 = "\Sigma_3 "
%format Sg_4 = "\Sigma_4 "
%format Sg_5 = "\Sigma_5 "
%format Sg_i = "\Sigma_i "
%format Signature = "\mathsf{Signature} "
%format Term = "\mathsf{Term} "
%format Type = "\mathsf{Type} "
%format Constraint = "\mathsf{Constraint} "
%format Context = "\mathsf{Context} "
%format t_0     = "t_0 "
%format t_1     = "t_1 "
%format t_2     = "t_2 "
%format t_3     = "t_3 "
%format u_1     = "u_1 "
%format u_2     = "u_2 "
%format v_1     = "v_1 "
%format v_2     = "v_2 "
%format Expect (a) = a
%format Fresh' (s) (g) (a) = "\textsc{Fresh}" (s, g, a)
%format Fresh (g) (a) = "\textsc{Fresh}" (g, a)
%format SolveState = "\mathsf{SolveState} "
%format elaborate = "\mathsf{elaborate} "
%format solve = "\mathsf{solve} "
%format check = "\mathsf{check} "
%format Map = "\mathsf{Map} "
%format MetaVar = "\mathsf{MetaVar} "
%format Maybe = "\mathsf{Maybe} "
%format $$ = "\cdot "
%format e_1 = "e_1 "
%format e_2 = "e_2 "
%format A_1 = "A_1 "
%format A_2 = "A_2 "
%format B_1 = "B_1 "
%format B_2 = "B_2 "
%format !! = "\ |\  "
%format delta = "\delta "
%format !--> = ^^ "\mapsto " ^^
%format head = "\mathsf{head} "
%format Vec = "\mathsf{Vec} "

%subst dummy = "\_ "

\title{Type checking through unification}
\author[1]{Francesco Mazzoli}
\affil[1]{Chalmers University}
\authorrunning{F. Mazzoli}

\Copyright{Francesco Mazzoli}

\subjclass{Classification}
\keywords{Keywords}

\serieslogo{}

\begin{document}
\maketitle

\begin{abstract}
  In this paper we describe how to take advantage of higher-order
  unification in a dependently typed language with meta-variables.  The
  literature usually presents the unification algorithm as a standalone
  component.  However the need to check definitional equality of terms
  while type checking gives rise to a tight interplay between type
  checking and unification.  We propose an algorithm that encodes a type
  checking problem entirely in the form of unification constraints, thus
  making the whole process simpler, more modular, and more
  understandable.
\end{abstract}

\section{Introduction}

Theories with dependent types have been successfully exploited to design
programming languages and theorem provers, such as Agda
\cite{norell2007}, Idris \cite{brady2013}, or Coq \cite{coqart}.  To
make these systems usable, the user is presented with a language much
richer than the underlying type theory, which will hopefully be small
enough to gain confidence in the correctness of the code that type
checks it.

One common way to make a type theory palatable is extending it with
\emph{meta-variables}, standing for yet to be determined terms, and
solved by unification.  Their usage in traditional programming languages
is confined to type inference, and thus traditionally they can stand in
for types only.  In dependently typed languages types can contain any
terms, and thus meta-variables are usually extended to stand in for any
term in our language.  A useful use case for meta-variables is
\emph{implicit arguments}, useful to avoid having to type easily
inferrable arguments to functions.  For example in Agda we can write a
safe |head| function extracting the first element, inferring both the
type of the elements and the length of the list:
\begin{code}
  head : {A : Set}{n : Nat} -> Vec A (1 + n) -> A
  head (x :: xs) = x
\end{code}
Where |Vec A n| denotes a list of length |n| with elements of type |A|,
and |Set| is the type of types.  The expression |{A : Set}{n : Nat}|
binds two implicit arguments.  When invoking |head|, the type-checker
will insert two meta-variables standing for |A| and |n|, that will
hopefully be solved by inspecting the |Vec| argument that follows.  Note
that |n| is a value, while in languages such ML and Haskell only types
can be implicit.\mytodo{Maybe use the term ``type scheme''?  That might
  be more familiar to people.}

The task of integrating meta-variables in a type checking algorithm for
dependent types gives rise to complications.  For example, consider the
task of type checking
\begin{code}
  true : if alpha <= 2 then Bool else Nat {-","-}
\end{code}
where |alpha| is an yet to be determined (\emph{uninstantiated})
meta-variable of type |Nat|.  We want the type of |true| to be |Bool|,
but reduction is impeded by |alpha|.  Thus, we cannot complete type
checking until |alpha| is instantiated.\footnote{Note that we cannot
  instantiate |alpha| without loss of generality, since both |0| and |1|
  are acceptable solutions.}  The key observation is that type checking
dependent types involves reducing terms to their normal forms, something
that can be affected by meta-variables, like in this case.\mytodo{Make
  it more clear that the key observation is that things can be
  obstructed, not that you need to normalize}

To solve problems like the one above, the only viable option---apart
from refusing to solve them---is to wait for the meta-variables that are
affecting type-checking to be instantiated, and then resume.  This gives
rise to a sort of concurrency that makes makes reasoning about the type
checking algorithm arduous.  In this paper we propose an algorithm that
statically encodes a type checking problem in a set of unification
constraints, generated through a static traversal of the term to be type
checked.  We expand on ideas developed in Agda \cite{norell2007} and
Epigram, \mytodo{Add citation for Epigram} but we simplify matters by
separating type checking and unification. \mytodo{Maybe state advantages
  more clearly---for example the fact that we need the unifier anyway,
  and we avoid an awful lot of work in the type-checker using my
  algorithm.} \mytodo{I should also give a nod to the work on Matita.}

In the rest of the paper, we will explain the problem more clearly
(section \ref{problem}).  Then we will introduce a simple type theory
(section \ref{type-theory}) that will serve as a vector to explain our
algorithm in detail.  The algorithm itself is presented in section
\ref{algorithm}, along with some of its properties. We will briefly
describe a unification procedure capable of solving the generated
constraints (section \ref{unification}), and briefly discuss how the
algorithm can be extended to support certain popular language features
(section \mytodo{Put section}). Finally, we give an overview on how the
ideas presented can be exploited to implement a full-fledged dependently
typed programming language (section \ref{big-picture}).  We have
implemented the presented algorithm in a prototype, \texttt{tog}, which
covers a subset of Agda -- every \texttt{tog} program is also a valid
Agda program.\footnote{The source code for \texttt{tog} is available at
  \url{https://github.com/bitonic/tog}.}

\section{The problem}
\label{problem}

In this section we will explain in more details the challenges faced
when type checking dependent types with meta-variables, and sketch a
solution.  An Agda-like syntax will be used throughout the examples,
please refer to appendix \ref{examples-syntax} for clarifications.

Going back to the problem of type checking
\begin{code}
  true : BoolOrNat alpha {-","-}
\end{code}
given
\begin{code}
  BoolOrNat : Nat -> Set
  BoolOrNat = \ x -> if x <= 2 then Bool else Nat

  alpha : Nat
  alpha = _ {-","-}
\end{code}
there are various tempting ways to approach the problem.  The most
conservative approach is to stop type checking when faced with
\emph{blocked} terms (terms whose \mytodo{whose?} normalization is
impeded by some meta-variables).  However, this approach is
unsatisfactory in many instances.

Consider
\begin{code}
  (true, refl) : BoolOrNat alpha * alpha == 0
\end{code}
Where |x == y| is the type inhabited by proofs that |x| is equal to |y|
(propositional equality), and |refl| is of type |t == t| for any |t|
(reflexivity).  Type checking this pair will involve type checking |true
: BoolOrNat alpha| and then |refl : alpha == 0|. If we give up on the
first type checking problem, we will not examine the second, which will
give us a solution for |alpha| (|alpha := 0|).  After instantiating
|alpha| we can easily go back and successfully type check the first
part.  In general, we want \mytodo{Another subjective statement.  I
  should encode the concept expressed in lemma \ref{algo-decidability}}
to attempt to type check as much as possible, to instantiate as many
meta-variables as possible.

Another approach is to assume that blocked type checking problems will
eventually be solved, and continue type checking.  However, this road is
dangerous since we need to be careful not to generate ill-typed terms or
invalid type checking contexts, as noted by
Norell \cite{norell2007}. \mytodo{Shouldn't Ulf and Catarina be cited
  here?}  Consider
\begin{code}
  test : alpha == 5 * (((x : BoolOrNat' alpha) -> BoolOrNat' (not x)) -> Nat)
  test = (refl, \ g -> g 0)
\end{code}
Type checking the definition |test| will involve checking that its type
is a valid type, and that its body is well typed.  Checking the former
will involve making sure that
\begin{code}
  BoolOrNat' alpha = Bool
\end{code}
since we know that the type of |x| must be |Bool|, given that |x| is
used as an argument of |not : Bool -> Bool|.\footnote{Note that checking
  that an equality type is a well-formed type does not involved checking
  that the equated things are equal---|4 == 5| is a perfectly valid
  type.  In this instance while |alpha == 5| appears in the type for
  |test|, this does not mean that |alpha| will be unified with |5| when
  type checking the type.  However, type checking its proof |refl :
  alpha == 5| will.}

If we assume that the the type is valid, we will proceed and type check
the body pairwise.  Type checking the first element---a proof by
reflexivity that |alpha| is equal to |5|---will instantiate |alpha|
to |5|, and then we will be faced with
\begin{code}
  (\ g -> g 0) : ((x : Nat) -> BoolOrNat' (not x)) -> Nat
\end{code}
Note that the type is ill-typed\footnote{|x|, of type |Nat|, appears as
  an argument to the boolean function |not|.}, violating the usual
invariants \mytodo{Please state the invariant(s).} present when type
checking.  Worse, to type check we will instantiate |x| with |0|, ending
up with |BoolOrNat' (not 0)|.  With some effort we can exploit this
problem to make the type checker loop,\mytodo{How? Perhaps such an
  example would be too long for inclusion in the paper, but the current
  text doesn't convince me that you (or someone else) have actually
  constructed such an example.}, and thus type checking will be
undecidable. \mytodo{Add less contrived example}

As mentioned in the introduction, at the heart of the problem lies the
fact that to type check we need to reduce terms to their weak head
normal form. If reduction is impeded by meta-variables, we cannot
proceed.  To overcome this problem, \mytodo{I'm certain that Norell
  added elaboration to overcome that problem, not so much about Conor.
  Integrate Conor's mail about the history of elaboration} McBride
\mytodo{Add citation if there is one} and then Norell proposed to define
type checking as an \emph{elaboration} \mytodo{I'm fairly certain that
  Conor wasn't the first person who employed elaboration
  techniques. Perhaps he (and James McKinna?) was the first to use it to
  tackle this problem, but I don't know. Feel free to ask him.}
procedure: given the problem of type checking |t| against |A| in context
|Gamma|, type checking will produce a term |t'| that approximates |t|:
\begin{code}
  Gamma !- t : A ~> t'
\end{code}
|t'| is an approximation of |t| in the sense that it it can be turned
into |t| by instantiating certain meta-variables---if a subterm of |t|
cannot be type checked a placeholder meta-variable will be put in its
place, an type checking that subterm will be postponed.  Type checking
will also consist in making sure that, once the postponed type checking
problems can be resumed solved, the placeholder meta-variables will be
instantiated accordingly with the corresponding omitted subterm of |t|
(possibly instantiated further).

For instance, when type checking the type of |test|, we'll have
\begin{code}
  nil  !-  ((x : BoolOrNat' alpha) -> BoolOrNat' (not x)) -> Nat  ^^ :  ^^ Set
       ~>  ((x : BoolOrNat' alpha) -> BoolOrNat' beta)    -> Nat
\end{code}
Since we cannot type check
\begin{code}
  x : BoolOrNat' alpha !- not x : Bool
\end{code}
a fresh meta-variable |beta| of type |Bool| in context |x : BoolOrNat'
alpha| is placed in the place of |not x|.  Then, when checking the body
of |test|, we will check it against the approximated type generated
above.  When |alpha| is instantiated, we can resume checking that
|BoolOrNat' alpha = Bool|, and if we are successful, instantiate |beta
:= not x|.  This will prevent us from running into problems when type
checking the body. \mytodo{Please explain how}

The Agda system, as described in Norell's thesis and according to the
current implementation, implements this elaboration interleaving type
checking and unification, using some fairly complicated machinery.  Our
contribution is to describe a type checking problem entirely in terms of
unification constraints, thus simplifying the algorithm. Unification,
the most complicated part of type checking, can be completely separated
from the logic that implements the typing rules. This modularity,
amongst the other advantages, makes it very easy to experiment with
different unification ``backends'' used by the same type checking
``frontend''.

\section{The type theory}
\label{type-theory}

\mytodo{Explain why we need spine syntax---for the same reason we need it
  in bidi type checking}

To present the type checking algorithm we will make use of a simple type
theory, whose syntax is shown in figure \ref{syntax}.  The theory is
designed to be the simplest fragment that presents the problems
described in section \ref{problem}.  For this reason we include a
universe |Set| and means of computing with booleans.  \footnote{Note that
  a simpler theory like Martin-L{\"o}f's logical framework is not
  affected by the problems we have mentioned in section \ref{problem},
  since we have no mean to compute types.}\mytodo{Is this footnote
  needed?}  The typing rules and algorithms presented in this paper can
be extended to richer theory, as we have done for our implementation,
which includes implicit arguments, user defined inductive data types and
records, and identity types.

Most operations are done under a context (denoted by |Gamma| or
|Delta|), that stores the types of free variables; and a signature |Sg|,
that stores the type and the body (if present) of defined constants.
Their syntax is shown in figure \ref{contexts-signatures}. In our case
we use the signature exclusively to store meta-variables, but in a real
language we would use it to store arbitrary definitions. We tacitly
assume that no duplicate names are present in contexts and signatures.
We make use of a global signature |Sg| throghout the rules---there is
no need for the rules to carry it explicitely since it is never changed.
Note that a signature contains only closed terms---we do not make use
of an explicit representation of meta-variables in context. This is for
the sake of simplicity, since we do not present our unification
algorithm in detail, where the contextual representation would be most
convenient. Throughout the paper, we will use |Gamma -> A| to indicate
the function type formed by all the types in |Gamma| as the domains, and
|t Gamma| to indicate the term formed by |t| applied to all the
variables in |Gamma|.

Neutral terms are represented in spine form, a necessary condition to
perform bidirectional type checking: if we want to type-check untyped
lambda abstractions, we need them to appear where we know what their
type should be, which will be the case if they appear as arguments of
types whose type is always inferrable. Note that while neutral terms are
denoted by |h (vec e)|, where |(vec e)| is a list of eliminators, we
adopt a more readable syntax when the eliminators are known---in their
syntax definition $\_$ denotes where the head will appear.

The only reduction rule we have is the one substituting instantiated
meta-variables by their body, as shown in figure \ref{reduction}.  When
doing so so, the spine form is immediately restored by using the rules
shown in figure \ref{elimination}, which assume the application is
well-typed.  Throughout the paper, we will liberally write |t (vec e)|
to indicate that |vec e| should be applied to |t| according to such
elimination rules.  Moreover, every term appearing in a derivation rule
is implicitly weak-head normalized. \mytodo{Explain what this means.}

The typing checking rules are shown in figure \ref{typing-rules}.  Every
mention of |Gamma| and |Sg| is assumed to be valid according to the
rules in figure \ref{context-signature-validity}.  Our type theory
includes a universe |Set| equipped with an inconsistent typing rule |Set
: Set| for the sake of simplicity, but our presentation can be extended
with stratified universes---or separating types and terms and adding a
dedicated ``large elimination'' rule.

Finally, the term conversion rules (needed to defined the typing rules)
are shown in figure \ref{conversion}.  The conversion rules are
performed in a type-directed way, so that it can respect the $eta$-laws
of functions. We separate conversion of terms and of lists of
eliminators, where
\[
|Gamma !- t : A !! vec e = vec d|
\]
indicates checking the equality of |vec e| and |vec d| with head |t|
of type |A|.  We need to carry the head forward since the conversion
rule for |ite| needs it.


\begin{figure}
  \begin{minipage}{.48\textwidth}
    \begin{code}
      A, B, C, t, u, v
            ::=  Set
            |    Bool | true | false
            |    (x : A) -> B | \ x -> t
            |    h (vec e)

      h     ::=  x | alpha

      e, d  ::=  ppa t | ite x A t u
    \end{code}
    % \begin{code}
    %   A, B, C, t, u, v
    %         ::=  Set                                          -- Type of types
    %         |    Bool | true | false                          -- Booleans
    %         |    (x : A) -> B | \ x -> t                      -- Dependent functions
    %         |    h (vec e)                                    -- Neutral term
  
    %   h     ::=  x                                            -- Variables
    %         |    alpha                                        -- Meta-variables
  
    %   e, d  ::=  ppa t                                        -- Function application
    %         |    ite x A t u                                  -- |Bool| elimination
    % \end{code}
    \caption{Terms, heads, and eliminators syntax.}
    \label{syntax}
  \end{minipage}%
  \quad\hfill
  \begin{minipage}{.48\textwidth}
    \begin{code}
      Gamma, Delta  ::= nil | Gamma; x : A                        
  
      Sg            ::= nil | Sg; alpha : A | Sg; alpha : A := t  
    \end{code}
    \caption{Context and signature syntax.}
    \label{contexts-signatures}
    \[
    \inference{|alpha : A := t `elem` Sg|}{
      |alpha (vec e) ~> t (vec e)|
    }
    \]
    \caption{\boxed{|t ~> u|} Term reduction}
    \label{reduction}
  \end{minipage}
\end{figure}

\begin{figure}
  \[
  \inference{}{
    |(h (vec e)) (vec d) ~> h (vec e) (vec d)|
  }\hfill
   \inference{|sub x u t (vec e) ~> h (vec d)|}{
     |(\ x -> t) u (vec e) ~> h (vec d)|
   }
  \]
  \[
  \inference{|t (vec e) ~> h (vec d)|}{
    |(ite x A t u true) (vec e) ~> h (vec d)|
  }\hfill
  \inference{|u (vec e) ~> h (vec d)|}{
    |(ite x A t u false) (vec e) ~> h (vec d)|
  }
  \]
  \caption{\boxed{|t (vec e) ~> h (vec d)|} Term elimination}
  \label{elimination}
\end{figure}

\begin{figure}
  \begin{minipage}{.48\textwidth}
    \[
    \inference{}{|Gamma !- Set <== Set|}\hfill
    \inference{}{|Gamma !- Bool <== Set|}
    \]
    \[
    \inference{}{|Gamma !- true <== Bool|}\hfill
    \inference{}{|Gamma !- false <== Bool|}
    \]
    \[
    \inference{|Gamma !- A <== Set| & |Gamma; x : A !- B <== Set|}{
      |Gamma !- (x : A) -> B <== Set|
    }
    \]
    \[
    \inference{|Gamma; x : A !- t <== B|}{|Gamma !- \ x -> t <== (x : A) -> B|}
    \]
    \[
    \inference{|Gamma !- h (vec e) ==> A| & |Gamma !- A = B : Set|}{
      |Gamma !- h (vec e) <== A|
    }
    \]
    \caption{\boxed{|Gamma !- t <== A|} Terms type checking}
    \label{rules-type-checking}
  \end{minipage}%
  \hfill
  \begin{minipage}{.48\textwidth}
      \[
      \inference{|x : A `elem` Gamma|}{
        |Gamma !- x nil ==> A|
      }\hfill
      \inference{|alpha : A `elem` Sg|}{
        |Gamma !- alpha nil ==> A|
      }
      \]
      \[
      \inference{|Gamma !- h (vec e) ==> (x : A) -> B| & |Gamma !- u <== A|}{
        |Gamma !- h ((vec e) u) ==> sub x (h (vec e)) B|
      }
      \]
      \[
      \inference{|Gamma !- h (vec e) ==> Bool| & |Gamma !- A <== Set|}{
        |Gamma !- ite x A t u (h (vec e)) ==> sub x (h (vec e)) A|
      }
      \]
      \caption{\boxed{|Gamma !- h (vec e) => A|} Neutral terms type inference}
      \label{rules-type-inference}
    \end{minipage}
\end{figure}

\begin{figure}
  \begin{minipage}{.48\textwidth}
    \[
    \inference{}{|!- nil|}\hfill
    \inference{
      |!- Gamma| & |Gamma !- A : Set|
    }{
      |!- Gamma; x : A|
    }
    \]
  \caption{\boxed{|!- Gamma|} Context validity}
  \label{context-validity}
  \end{minipage}%
  \hfill
  \begin{minipage}[b]{0.48\textwidth}
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
  \caption{\boxed{|!- Sg|} Signature validity}
  \label{signature-validity}
  \end{minipage}
\end{figure}

\begin{figure}
  % \begin{subfigure}[b]{1\textwidth}
  \[
  \inference{}{|Gamma !- Set = Set : Set|}\hfill
  \inference{}{|Gamma !- Bool = Bool : Set|}\hfill
  \inference{}{|Gamma !- true = true : Bool|}
  \]
  \[
  \inference{}{|Gamma !- false = false : Bool|}\hfill
  \inference{|Gamma !- A_1 = A_2 : Set| & |Gamma; x : A_1 !- B_1 = B_2 : Set|}{
    |Gamma !- (x : A_1) -> B_1 = (x : A_2) -> B_2 : Set|
  }
  \]
  \[
  \inference{|Gamma; x : A !- f x = g x : B|}{|Gamma !- f = g : (x : A) -> B|}\hfill
  \inference{|Gamma !- h ==> A| & |Gamma !- h ^ nil : A !! vec e = vec d|}{
    |Gamma !- h (vec e) = h (vec d)|
  }
  \]
  \caption{\boxed{|Gamma !- t = u : A|} Term conversion}
  \label{term-conversion}
\end{figure}
\begin{figure}
  \[
  \inference{}{|Gamma !- t : A !! nil = nil|}\hfill
  \inference{|Gamma !- u = v : A| & |Gamma !- t u : sub x t B !! vec e = vec d|}{
    |Gamma !- t : (x : A) -> B !! u (vec e) = v (vec d)|
  }
  \]
  \[
  \inference{
    |Gamma;x : Bool !- A = B : Set| &
    |Gamma !- u_1 = u_2 : sub x true A| & |Gamma !- v_1 = v_2 : sub x false A| \\
    |Gamma !- ite x A u_1 v_1 t : sub x t A !! e = d|
  }{
    |Gamma !- t : Bool !! (ite x A u_1 v_1) (vec e) = (ite x B u_2 v_2) (vec d)|
  }
  \]
  \caption{\boxed{|Gamma !- t : A !! (vec e) = (vec d)|} Spine conversion}
  \label{spine-conversion}
\end{figure}

\mytodo[inline]{Maybe mention some property of the type theory?
  Normalization, decidability of type checking, etc?}

\section{The algorithm}
\label{algorithm}

As mentioned in section \ref{problem}, our algorithm will elaborate a
type checking problem into a well typed term and a set of unification
constraints.

More specifically, we will elaborate a type checking problem into a well
typed term and a set unification constraints, along with an updated
signature:
\begin{code}
  << Sg, Gamma !- t : A >> ~> Sg', u, Con
\end{code}
Where the |Con| is a set of heterogeneous unification constraints
\mytodo{Explain what a constraint is somewhere.} of the form
\begin{code}
  Gamma !- t : A = u : B
\end{code}
\mytodo{Explain what solving those constraints mean.}

We observe that our rules always monotonically augment the signature by
adding new meta-variables.  Moreover, when elaborating type-checking
problem |Gamma !- t : A|, every rule generates a fresh meta-variable
|alpha : Gamma -> A|, and returns the union of all the constraints
generated in the premise plus |{Gamma !- alpha : A = u : B}|, for some
term |t| and type |B|---intuitively we want |t : A| to be |u : B|.  For
these reasons, we will write our rules in the following style:
\[
\inference{
  |<< Gamma_1 !- u : B >> ~> u'| & |<< Gamma_2 !- v : C >> ~> v'| \\
}{
  |<< Gamma_4 !- t : A >> ~> t' , A' >>|
}
\]
standing for the much more tiresome
\[
\inference{
  |<< Sg_1, Gamma_1 !- u : B >> ~> Sg_2, u', Con_1| &
  |<< Sg_2, Gamma_2 !- v : C >> ~> Sg_3, v', Con_2| \\
  |Sg_3, alpha := Fresh' Sg_4 Gamma A|
}{
  |<< Sg_4 , Gamma_4 !- t : A >> ~> Sg_5, t, {Gamma !- t' : A' = alpha : A} `union` Con_1 `union` Con_2|
}
\]
Where |Fresh' Sg Gamma A| stands for
\begin{code}
Sg; alpha : Gamma -> A, ^^ alpha Gamma {-","-}
\end{code}
|alpha| being a fresh name in |Sg|.  Similarly, we will use
|Fresh| without mentioning the signature.

The full rules are shown in figure \ref{elaboration}.  They are
remarkably similar to the typing rules, however instead of matching
directly on the type we expect we match through constraints.  For
example, when elaborating |nil !- true : A|, we will get back a
meta-variable |alpha| together with constraint
\begin{code}
  nil !- true : Bool = alpha : A
\end{code}
If |A| is indeed |Bool|, the constraint will be immediately solvable and
|alpha| will be instantiated to |true|, thus giving back our original
term. If on the other hand |A| cannot be proved equal to |Bool|
immediately, for example if it is |BoolOrNat beta|, the unifier will not
succeed and thus instantiate |alpha| until the types are proved
equal---and until that moment |alpha| will be used in place of |true|.

When we need to match on a type with subterms, we do it by creating
fresh meta-variables to match the subterms---see the rules for lambda
abstractions and application.  For example, when elaborating problem
|nil !- \ x -> x : A|, we will get back a meta-variable |alpha| together
with constraints
\begin{code}
  nil !- (\ x -> delta x) : (x : beta) -> gamma x = alpha : A
  nil; x : beta !- x : beta = delta x : gamma x
\end{code}
Where
\begin{code}
  alpha : A
  beta : Set
  gamma : beta -> Set
  delta : beta -> gamma
\end{code}
Note how these constraints encode the fact that we are type-checking the
identity function, since we are equating |beta| to |gamma x| in the
second constraint.  If the provided type is wrong, for example if |A =
Bool| or |A = Bool -> Bool -> Bool| unification will fail on the first
and second constraint, respectively.  If the type is correct, for
example if it is |Bool -> Bool|, all the constraints are solvable by
pattern unification, resulting in
\begin{code}
  beta := Bool
  gamma := \ x -> Bool
  alpha := \ x -> delta x
  delta := \ x -> x
\end{code}

\begin{figure}
  \[
  \inference{}{
    |Gamma !- Set : A ~> Expect (Set : Set)|
  }\quad
  \inference{}{
    |Gamma !- Bool : A ~> Expect (Bool : Set)|
  }
  \]
  \[
  \inference{}{
    |Gamma !- true : A ~> Expect (true : Bool)|
  }\quad
  \inference{}{
    |Gamma !- false : A ~> Expect (false : Bool)|
  }
  \]
  \[
  \inference{
    |Gamma !- A : Set ~> A'| & |Gamma; x : A' !- B : Set ~> B'|
  }{
    |Gamma !- (x : A) -> B : S ~> Expect ((x : A') -> B' : Set)|
  }
  \]
  \[
  \inference{
    |beta : Fresh Gamma Set| & |gamma : Fresh (Gamma; x : beta) Set| \\
    |Gamma; x : beta !- t : gamma ~> t'|
  }{
    |Gamma !- \ x -> t : A ~> Expect ((\ x -> t') : (x : beta) -> gamma)|
  }
  \]
  \[
  \inference{
    |x : A `elem` Gamma|
  }{
    |Gamma !- x nil ~> Expect (x nil : A)|
  }\quad
  \inference{
    |alpha : A `elem` Sg|
  }{
    |Gamma !- alpha nil ~> Expect (alpha nil : A)|
  }\quad
  \]
  \[
  \inference{
    |beta : Fresh Gamma Set| & |gamma : Fresh (Gamma; x : beta) Set| \\
    |Gamma !- h (vec e) : (x : beta) -> gamma ~> t| &
    |Gamma !- u : beta ~> u'|
  }{
    |Gamma !- h ((vec e) u) : A ~> Expect (t u' : sub x u' gamma)|
  }
  \]
  \[
  \inference{
    |Gamma; x : Bool !- B : Set ~> B'| & |Gamma !- h (vec e) : Bool ~> t| \\
    |Gamma !- u : sub x true B' ~> u'| & |Gamma !- v : sub x false B' ~> v'|
  }{
    |Gamma !- ite x B u v (h (vec e)) : A ~> Expect (ite x B' u' v' t : sub x t B')|
  }
  \]
  \caption{\boxed{|Sg, Gamma !- t : A ~> Sg',u,Con|} Elaboration}
  \label{elaboration}
\end{figure}

\subsection{Some properties}

\begin{lemma}[Well typedness]
  If
  \begin{code}
    << Sg, Gamma !- t : A >> ~> Sg', u, Con {-","-}
  \end{code}
  then
  \begin{code}
    Gamma !- u : A
  \end{code}
\end{lemma}

Follows immediately from the rules in figure \ref{elaboration}, since
each rule creates a fresh meta-variable of the required type.

\begin{lemma}[Restoring equality]
  If
  \begin{code}
    << Sg_1, Gamma !- t : A >> ~> Sg_2, u, Con {-","-}
  \end{code}
  and unification solves all the constraints in |Con|, generating new
  signature |Sg_3|, then
  \begin{code}
    Sg_3, Gamma !- t : A
    Sg_3, Gamma !- t = u : A
  \end{code}
\end{lemma}

Follows by induction on the term |t|.

\begin{lemma}[Decidability of type checking]
  \label{algo-decidability}
  If
  \begin{code}
    << Sg_1, Gamma !- t : A >> ~> Sg_2, u, Con {-","-}
  \end{code}
  and unification cannot solve all the constraints in |Con|, then there
  is no valid typing derivation for |t| in some signature |Sg_3| which
  is an extension of |Sg_1| without instantiating meta-variables in
  |Sg_1| without loss of generality.
\end{lemma}

How do we prove this?

\section{Unification?}
\label{unification}

We described how the elaboration procedure generates constraints of the
form
\begin{code}
  Gamma !- t : A = u : B {-","-}
\end{code}
where solving the constraint means proving both |A| and |B| and |t| and
|u| definitionally equal, possibly by instanting meta-variables.

Heterogenous constraints are needed to have the elaboration algorithm to
produce a set of ``flat'' constraints, without having to record
dependencies between them.  Moreover, a complete unification algorithm
for dependent types will need to be heterogeneous, as we will explain.
\mytodo{Insert Conor citation}

Since the unifier will need to instantiate and add new meta-variables,
it will need to update the signature.  Thus, 

\section{The big picture}
\label{big-picture}

\begin{code}
  -- A signature storing types and maybe bodies for meta-variables.
  type Signature = Map MetaVar (Type, Maybe Term)

  -- A context for de Bruijn variables.
  type Context = [Type]

  -- Type checking.
  check :: Signature -> Context -> Term -> Type -> Bool

  -- Elaboration.
  data Constraint = Constraint Context Term Type Term Type
  elaborate  ::  Signature -> Context -> Term -> Type
             ->  (Signature, Term, [Constraint])

  -- Unification.
  data SolveState
  solve :: SolveState -> [Constraint] -> SolveState
\end{code}

\section{Bidirectional type checking}

\appendix
\section{Examples syntax}
\label{examples-syntax}

\mytodo{Actually write the syntax}

Include: |_ == _|, |refl|, |*|, pattern matching, implicits...

\section{Unification algorithm}

\begin{figure}
  \begin{code}
    Gamma  !-  alpha (vec x)   : A  =  Delta !- alpha (vec y)  : B   !-->   intersect
    Gamma  !-  alpha (vec x)   : A  =  Delta !- t              : B   !-->   assign
    Gamma  !-  t               : A  =  Delta !- alpha (vec y)  : B   !-->   assign

    Gamma  !-  Set    : Set   =    Delta  !- Set    : Set   !-->  empty
    Gamma  !-  Bool   : Set   =    Delta  !- Bool   : Set   !-->  empty
    Gamma  !-  true   : Bool  =    Delta  !- true   : Bool  !-->  empty
    Gamma  !-  false  : Bool  =    Delta  !- false  : Bool  !-->  empty

    (Gamma  !- (x : A_1) -> B_1 : Set) = (Delta !- (x : A_2) -> B_2 : Set) !-->
      ^^  {  ^^  (Gamma !- A_1 : Set) = (Delta !- A_2 : Set)
          ,      (Gamma; x : A_1 !- B_1 : Set) = (Delta; x : A_2 !- B_2 : Set) ^^ }

    (Gamma !- t : (x : A_1) -> B_1) = (Delta !- u : (x : A_2) -> B_2) !-->
      ^^  { ^^ (Gamma; x : A_1 !- t x : B_1) = (Gamma; x : A_2 !- u x : B_2) ^^ }

    (Gamma !- h (vec e) : _) = (Delta !- h (vec d) : _) !-->
          (Gamma !- h nil : A !! vec e) = (Delta !- h nil : B !! vec d)

    (Gamma !- t : A) = (Delta !- u : B) !--> Bot
  \end{code}

  \begin{code}
    (Gamma !- t : _ !! nil) = (Delta !- t : _ !! nil) !--> empty

    (Gamma !-  t_1 : (x : A_1) -> B_1 !! u_1 (vec e_1)) = (Delta !- t_2 : (x : A_2) -> B_2 !! u_2 (vec e_2)) !-->
      ^^  {(Gamma !- u_1 : A_1) = (Delta !- u_2 : A_2)} `union`
          (Gamma !-  t_1 u_1 : sub x u_1 B_1 !! vec e_1) = (Delta !- t_2 u_2 : sub x u_2 B_2 !! vec e_2)

    (Gamma !- t_1 : Bool !! (ite x A_1 u_1 v_1) (vec e_1))
      =
    (Gamma !- t_2 : Bool !! (ite x A_2 u_2 v_2) (vec e_2)) !-->
      ^^  {  (Gamma;x : Bool !- A_1 : Set) = (Delta;x : Bool !- A_2 : Set)
          ,  (Gamma !- u_1 : sub x true A_1) = (Delta !- u_2 : sub x true A_2)
          ,  (Gamma !- v_1 : sub x false A_1) = (Delta !- v_2 : sub x false A_2) ^^ } `union`
          (Gamma !- ite x A_1 u_1 v_1 t_1 : sub x t_1 A_1 !! (vec e_1))
             =
          (Delta !- ite x A_2 u_2 v_2 t_2 : sub x t_2 A_2 !! (vec e_2))

    (Gamma !- t : A !! vec e) = (Delta !- u : B !! vec d) !--> Bot
  \end{code}
\end{figure}

\bibliographystyle{plain}
\bibliography{type-checking-metas}

\end{document}
