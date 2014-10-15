\documentclass{beamer}
\usepackage[sc,slantedGreek]{mathpazo}
\usepackage{bussproofs}
%include polycode.fmt

%format forall = "\forall "
%format alpha = "\alpha "
%format beta = "\beta "
%format Sigma = "\Sigma "
%format Nat = "\mathbb{N} "
%format Set = "\mathsf{Set} "
%format Bool = "\mathsf{Bool} "
%format true = "\mathbf{true} "
%format false = "\mathbf{false} "
%format Unit = "\mathsf{Unit} "
%format Gamma = "\Gamma "
%format !- = "\vdash "
%format Ctxt = "\mathsf{Ctxt} "
%format Type = "\mathsf{Type} "
%format Expr = "\mathsf{Expr} "
%format Term = "\mathsf{Term} "
%format ~> = "\leadsto "
%format CtxEmpty = "\cdot "
%format refl = "\mathbf{refl} "
%format test_1 = "test_1 "
%format test_2 = "test_2 "
%format test_3 = "test_3 "
%format Constraint = "\mathsf{Constraint} "
%format e_0 = "e_0 "
%format << = "\llbracket "
%format >> = "\rrbracket "
%format ~= = "\cong "
%format e_1 = "e_1 "
%format e_2 = "e_2 "
%format cs_1 = "cs_1 "
%format cs_2 = "cs_2 "
%format List = "\mathsf{List} "
%format >>- = "\ \sequ \ "
%format && = "\ \wedge \ "
%format Delta = "\Delta "

\title{Type checking in the presence of meta-variables (reprise)}
\author{Francesco Mazzoli}
\date{October 2014}

\begin{document}
\frame{\titlepage}

\begin{frame}
  \frametitle{Meta-variables and dependent types}

  Used for inference:

  \begin{code}
    length : forall {A} -> List A -> Nat
    length []         = 0
    length (x :: xs)  = 1 + length xs
  \end{code}
  
  The type becomes

  \begin{code}
    length : {A : Set} -> List A -> Nat
  \end{code}

  And in invocations the type will be filled in automatically: |length
  [1,2,3]| $\Rightarrow$ |length _ [1,2,3]| $\Rightarrow$ |length Nat
  [1,2,3]|

\end{frame}

\begin{frame}
  \frametitle{How does it work?}

  We want to instantiate meta-variables as needed when type checking
  some terms. \\~\\

  This is usually accomplished in an on-demand fashion: when trying to
  check equality between two terms in type checking we will instantiate
  them accordingly if they are meta-variables.
\end{frame}

\begin{frame}
  \frametitle{How does it work?}

  \begin{code}
    length : {A : _} -> List A -> Nat
  \end{code}

  |_| will introduce a new meta-variable, say |alpha|.  \\~\\

  The application of |alpha| to |List : Set -> Set| will prompt the type
  checker to check |alpha = Set|, thus instantiating the meta-variable.
\end{frame}

\begin{frame}
  \frametitle{Inconveniences}

  Given
  \begin{code}
    Foo : Bool -> Set
    Foo true   = Bool
    Foo false  = Nat
  \end{code}

  and
  \begin{code}
    alpha : Bool
    alpha = _
  \end{code}

  How should we proceed when faced with definition
  \begin{code}
    test_1 : Foo alpha
    test_1 = true
  \end{code}

  ?
\end{frame}

\begin{frame}
  \frametitle{Why can't we just give up?}

  It's tempting to just stop when facing such problems.\\~\\

  However, consider
  \begin{code}
    test_2 : (Foo alpha, alpha == true)
    test_2 = (true, refl)
  \end{code}

  We don't want to stop when type checking |true : Foo alpha|, because
  checking |refl : alpha == true| will let us type check the whole
  definition.
\end{frame}

\begin{frame}
  \frametitle{Why can't we just pretend things are fine?}

  In the previous example:
  \begin{code}
    test_2 : (Foo alpha, alpha == true)
    test_2 = (true, refl)
  \end{code}

  Can't we just pretend we have checked |true : Foo alpha| and continue?

  It doesn't work in the general case, consider
  \begin{code}
    test_3 : ((x : Foo alpha) -> Foo (not x)) -> Nat
    test_3 = \ g -> g 0
  \end{code}

  We'll generate constraints |Foo alpha == Bool|, since |x : Bool|.  If
  we just continue and try to type check the body, we'll get the
  ill-typed |not 0| by instantiating |x|.\\~\\

  So, we need to be more careful.
\end{frame}

\begin{frame}
  \frametitle{Elaborate!}

  Type checking will take a lump of syntax (|Expr|) and give us
  back a term:

  \begin{code}
    check : Ctxt -> Type -> Expr -> Term
  \end{code}

  The idea is that in |check Gamma A e ~> t| the resulting |t|
  might be only an approximation of the original |e|.
\end{frame}

\begin{frame}
  \frametitle{Elaborate!}

  |check| will insert meta-variables when type checking is ``stuck'',
  which will be instantiated when type checking will be able to resume. \\~\\

  Going back to
  \begin{code}
    test_1 : Foo alpha
    test_1 = true
  \end{code}

  Type checking the body of the definition we get
  \begin{code}
    check CtxEmpty (Foo alpha) true ~> beta
  \end{code}

  Where
  \begin{code}
    beta : Foo alpha
  \end{code}

\end{frame}

\begin{frame}
  \frametitle{Elaborate!}

  |check| will add constraints to ensure that if possible we'll type
  check the original term fully.\\~\\

  Going back to

  \begin{code}
    check CtxEmpty (Foo alpha) true ~> beta
  \end{code}

  We want to resume type checking when |Foo alpha| is unblocked, and if
  we succeed instantiate |beta| to the original term:
  \begin{code}
    beta := true
  \end{code}
\end{frame}

\begin{frame}
  \frametitle{Things get messy}
  
  How exactly to handle this elaboration works is the question.\\~\\

  Ulf's thesis, chapter 3, provides an account on how to do this -- an
  approach then developed in Agda.\\~\\

  A lot of poorly documented work in this direction has been done in
  Epigram and Epigram2.
\end{frame}

\begin{frame}
  \frametitle{How it works in Agda}

  It's pretty messy, but the basic idea is to type check normally, but
  stopping and inserting meta-variables when unification is stuck.\\~\\

  We then need to put some quite complicated machinery in place to
  resume checking when needed, instantiate ``placeholder'' variables,
  etc.
\end{frame}

\begin{frame}
  \frametitle{Let the unifier do all the work}

  The idea is to convert a type checking problem
  \begin{code}
    Gamma !- e : A
  \end{code}

  Into a list of heterogeneous unification problems, of the form
  \begin{code}
    Gamma !- t : A ~= u : B
  \end{code}

  Intuitively, by looking at the expression to check we build up a
  series of constraints that make sure that |A| has the right shape.
\end{frame}

\begin{frame}
  \frametitle{Let the unifier do all the work}

  We can give this elaboration procedure a simple type:
  \begin{code}
    -- I'll use |Gamma !- t : A ~= u : B| as a nicer notation
    data Constraint = Constraint Ctxt Term Type Term Type
  \end{code}

  \begin{code}
    -- I'll use | << Gamma !- e : A >> | as a nicer notation
    elaborate : Ctxt -> Type -> Expr -> TC (Term, [Constraint])
  \end{code}

  |TC| is some monad that lets us add meta-variables:
  \begin{code}
    newMeta : Ctxt -> Type -> TC Term
  \end{code}
\end{frame}

\begin{frame}
  \frametitle{|Expr|}

  We'll write the elaboration much like we'd write a type checker
  without meta-variables.\\~\\

  Given a simple type expression type

  \begin{code}
    data Expr
       =   x                       -- Variable
       |   _                       -- Meta-variable
       |   Set                     -- Type of types
       |   (x : Expr) -> Expr      -- Function type
       |   \ x -> Expr             -- Abstraction
       |   Expr Expr               -- Function application
  \end{code}
\end{frame}

\begin{frame}
  \frametitle{|Term|}

  And terms

  \begin{code}
    data Term
       =   x                       -- Variable
       |   alpha                   -- Meta-variable
       |   Set                     -- Type of types
       |   (x : Term) -> Term      -- Function type
       |   \ x -> Term             -- Abstraction
       |   Term Term               -- Function application
  \end{code}

  \begin{code}
    type Type = Term
  \end{code}

\end{frame}

\begin{frame}
  \frametitle{Variables, meta-variables, |Set|}

  % \hspace*{-20pt}
  \begin{minipage}[t]{0.48\linewidth}
    \begin{code}
      << Gamma !- x : A >> = do
        let B = lookup x Gamma
        t <- newMeta Gamma A
        return (t, [Gamma !- x : B ~= t : A])
    \end{code}
  \end{minipage}%
  \hfill%
  \begin{minipage}[t]{0.48\linewidth}
    \begin{prooftree}
      \AxiomC{|x : A `elem` Gamma|}
      \UnaryInfC{|Gamma !- x : A|}
    \end{prooftree}
  \end{minipage}

  \begin{code}
    << Gamma !- _ : A >> = do
      t <- newMeta Gamma A
      return (t, [])
  \end{code}

  \begin{minipage}[t]{0.48\linewidth}
    \begin{code}
      << Gamma !- Set : A >> = do
        t <- newMeta Gamma A
        return (t, [Gamma !- Set : Set ~= t : A])
    \end{code}
  \end{minipage}%
  \hfill%
  \begin{minipage}[t]{0.48\linewidth}
    \begin{prooftree}
      \AxiomC{}
      \UnaryInfC{|Gamma !- Set : Set|}
    \end{prooftree}
  \end{minipage}

\end{frame}

\begin{frame}
  \frametitle{Dependent function type}

  \begin{prooftree}
    \AxiomC{|Gamma !- Dom : Set|}
    \AxiomC{|Gamma; x : Dom !- Cod : Set|}
    \BinaryInfC{|Gamma !- (x : Dom) -> Cod : Set|}
  \end{prooftree}

  \begin{code}
    << Gamma !- (x : Dom) -> Cod : A >> = do
      (Dom', cs_1) <- << Gamma !- Dom : Set >>
      (Cod', cs_2) <- << Gamma; x: Dom' !- Cod : Set >>
      t <- newMeta Gamma A
      let c = Gamma !- ((x : Dom') -> Cod') : Set = t : A
      return (t, c :: (cs_1 ++ cs_2))
  \end{code}
\end{frame}

\begin{frame}
  \frametitle{Abstractions}

  \begin{prooftree}
    \AxiomC{|Gamma; x : Dom !- t : Cod|}
    \UnaryInfC{|Gamma !- \ x -> t : (x : Dom) -> Cod|}
  \end{prooftree}

  \begin{code}
    << Gamma !- (\x -> e) : A >> = do
      Dom <- newMeta Gamma Set
      Cod <- newMeta (Gamma; x: Dom) Set
      (body, cs) <- << Gamma; x: Dom !- e : Cod >>
      t <- newMeta Gamma A
      let c = Gamma !- (\x -> body) : ((x : Dom) -> Cod) ~= t : A
      return (t, c :: cs)
  \end{code}
\end{frame}

\begin{frame}
  \frametitle{Application}

  \begin{prooftree}
    \AxiomC{|Gamma !- f  : (x : Dom) -> Cod|}
    \AxiomC{|Gamma !- arg : Dom|}
    \BinaryInfC{|Gamma !- f arg : Cod[x := arg]|}
  \end{prooftree}

  \begin{code}
    << Gamma !- e_1 e_2 : A >> = do
      Dom <- newMeta Gamma Set
      Cod <- newMeta (Gamma; x: Dom) Set
      (f, cs_1) <- << Gamma !- e_1 : (x : Dom) -> Cod >>
      (arg, cs_2) <- << Gamma !- e_2 : Dom >>
      t <- newMeta Gamma A
      let c = Gamma !- (f arg) : Cod[x := arg] = t : A
      return (t, c :: (cs_1 ++ cs_2))
  \end{code}
\end{frame}

% \begin{frame}
%   \frametitle{The big picture}

%   \begin{code}
%     data Expr
% \end{frame}

\begin{frame}
  \frametitle{What about unification?}

  We have constraints of the form
  \begin{code}
    Gamma !- t : A ~= u : B
  \end{code}

  We can convert them to homogeneous constraints
  \begin{code}
    Gamma !- A ~= B : Set >>- Gamma !- t ~= u : A
  \end{code}

  Where |>>-| is a sequencing operator that has the unifier solve the
  first constraint before attempting the second.\\~\\

  But we lose solutions -- the types might be similar enough to advance
  unification of the terms, while with homogeneous equality we demand
  the types to be equal first.
\end{frame}

\begin{frame}
  \frametitle{What about unification?}

  We can also leave the constraints as they are, and have the unifier
  solve heterogeneously, by making sure that the types have a rigid head
  before trying to compare the head of the terms.

  \begin{code}
    Gamma !- t : A ~= u : B
  \end{code}

  Becomes
  \begin{code}
    Gamma !- t : A ~= u : B && Gamma !- A : Set ~= B : Set
  \end{code}

  However, we still lose solutions.\\~\\
\end{frame}

\begin{frame}
  \frametitle{What about unification?}

  Consider what happens when unifying
  \begin{code}
    Gamma !- (\ x -> t) : (x : A) -> B ~= (\ x -> u) : (x : S) -> T
  \end{code}

  We'd like to go ahead and compare the bodies...
  \begin{code}
    Gamma; x : ? !- t : B[x := ?] ~= u : T[x := ?]
  \end{code}

  With one context, we need to make sure that |A ~= B| first.
\end{frame}

\begin{frame}
  \frametitle{What about unification?}

  Gundry \& McBride solved this problem with ``twin variables''.\\~\\

  I think it's simpler to just keep two contexts:
  \begin{code}
    (Gamma !- (\ x -> t) : (x : A) -> B) ~= (Delta !- (\ x -> u) : (x : S) -> T)
  \end{code}
  Becomes
  \begin{code}
    (Gamma; x : A !- t : B) ~= (Delta; x : S !- u : T)
  \end{code}
\end{frame}

\begin{frame}
  \frametitle{What about bidirectional type checking?}

  What to do about
  \begin{itemize}
    \item Implicit arguments;
    \item Overloaded constructors;
    \item Type classes (canonical structures);
    \item ...
    \end{itemize}
\end{frame}

\end{document}
