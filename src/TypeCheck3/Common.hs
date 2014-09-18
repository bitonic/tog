{-# LANGUAGE OverloadedStrings #-}
module TypeCheck3.Common where

import           Prelude                          hiding (abs, pi)

import qualified Data.HashSet                     as HS

import           Prelude.Extended
import           Syntax.Internal                  (Name)
import qualified Syntax.Internal                  as A
import           Term
import           Term.Context                     (Ctx)
import qualified Term.Context                     as Ctx
import qualified Term.Signature                   as Sig
import qualified Term.Telescope                   as Tel
import           PrettyPrint                      (($$), (<+>), (//>), (//), group, hang)
import qualified PrettyPrint                      as PP
import           TypeCheck3.Monad

-- Errors
---------

data CheckError t
    = ExpectingEqual (Type t)
    | ExpectingPi (Type t)
    | ExpectingTyCon Name (Type t)
    | FreeVariableInEquatedTerm MetaVar [Elim t] (Term t) Var
    | NameNotInScope Name
    | OccursCheckFailed MetaVar (Closed (Term t))
    | SpineNotEqual (Type t) [Elim t] (Type t) [Elim t]
    | TermsNotEqual (Type t) (Term t) (Type t) (Term t)
    | PatternMatchOnRecord A.Pattern Name -- Record type constructor

checkError :: (IsTerm t) => CheckError t -> TC t s a
checkError err = typeError =<< renderError err

renderError :: (IsTerm t) => CheckError t -> TC t s PP.Doc
renderError err =
  case err of
    TermsNotEqual type1 t1 type2 t2 -> do
      t1Doc <- prettyTermTC t1
      type1Doc <- prettyTermTC type1
      t2Doc <- prettyTermTC t2
      type2Doc <- prettyTermTC type2
      return $
        t1Doc <+> ":" <+> type1Doc $$
        PP.nest 2 "!=" $$
        t2Doc <+> ":" <+> type2Doc
    SpineNotEqual type1 es1 type2 es2 -> do
      type1Doc <- prettyTermTC type1
      es1Doc <- prettyElimsTC es1
      type2Doc <- prettyTermTC type2
      es2Doc <- prettyElimsTC es2
      return $
        es1Doc <+> ":" <+> type1Doc $$
        PP.nest 2 "!=" $$
        es2Doc <+> ":" <+> type2Doc
    FreeVariableInEquatedTerm mv els rhs v -> do
      mvDoc <- prettyTermTC =<< metaVarTC mv els
      rhsDoc <- prettyTermTC rhs
      return $ "Free variable `" PP.<> prettyVar v PP.<> "' in term equated to metavariable application:" $$
               mvDoc $$ PP.nest 2 "=" $$ rhsDoc
    OccursCheckFailed mv t -> do
      tDoc <- prettyTermTC t
      return $ "Attempt at recursive instantiation:" $$ PP.pretty mv <+> ":=" <+> tDoc
    NameNotInScope name -> do
      return $ "Name not in scope:" <+> PP.pretty name
    PatternMatchOnRecord synPat tyCon -> do
      return $ "Cannot have pattern" <+> PP.pretty synPat <+> "for record type" <+> PP.pretty tyCon
    ExpectingPi type_ -> do
      typeDoc <- prettyTermTC type_
      return $ "Expecting a pi type, not:" //> typeDoc
    ExpectingEqual type_ -> do
      typeDoc <- prettyTermTC type_
      return $ "Expecting an identity type, not:" //> typeDoc
    ExpectingTyCon tyCon type_ -> do
      typeDoc <- prettyTermTC type_
      return $ "Expecting a" <+> PP.pretty tyCon PP.<> ", not:" //> typeDoc
  where
    prettyVar = PP.pretty


-- MetaVar handling
------------------------------------------------------------------------

addMetaVarInCtx
  :: (IsTerm t)
  => Ctx t -> Type t -> TC t s (Term t)
addMetaVarInCtx ctx type_ = do
  mv <- addMetaVar =<< ctxPiTC ctx type_
  ctxAppTC (metaVar mv []) ctx


-- Whnf'ing and view'ing
------------------------

nfTC :: (IsTerm t) => t -> TC t s t
nfTC t = withSignatureTermM $ \sig -> nf sig t

nf'TC :: (IsTerm t, Nf f) => f t -> TC t s (f t)
nf'TC t = withSignatureTermM $ \sig -> nf' sig t

whnfTC :: (IsTerm t) => t -> TC t s (Blocked t)
whnfTC t = withSignatureTermM $ \sig -> whnf sig t

whnfViewTC :: (IsTerm t) => t -> TC t s (TermView t)
whnfViewTC t = withSignatureTermM $ \sig -> whnfView sig t

-- Telescope & context utils
----------------------------

-- telStrengthen :: (IsTerm f) => Tel.IdTel f (Suc v) -> TermM (Maybe (Tel.IdTel f v))
-- telStrengthen (Tel.Empty (Tel.Id t)) =
--   fmap (Tel.Empty . Tel.Id) <$> strengthen t
-- telStrengthen (Tel.Cons (n, t) tel0) = runMaybeT $ do
--   t' <- MaybeT $ strengthen t
--   tel' <- MaybeT $ telStrengthen tel0
--   return $ Tel.Cons (n, t') tel'

-- | Collects all the variables in the 'Ctx.Ctx'.
ctxVars :: forall t. (IsTerm t) => Ctx.Ctx (Type t) -> [Var]
ctxVars = reverse . go 0
  where
    go :: Int -> Ctx.Ctx (Type t) -> [Var]
    go _ Ctx.Empty                 = []
    go ix (Ctx.Snoc ctx (name, _)) = V (named name ix) : go (ix + 1) ctx

-- | Creates a 'Pi' type containing all the types in the 'Ctx' and
-- terminating with the provided 't'.
ctxPi :: IsTerm t => Ctx (Type t) -> Type t -> TermM (Type t)
ctxPi Ctx.Empty                  t = return t
ctxPi (Ctx.Snoc ctx (_n, type_)) t = ctxPi ctx =<< pi type_ t

-- | Creates a 'Lam' term with as many arguments there are in the
-- 'Ctx.Ctx'.
ctxLam :: IsTerm t => Ctx (Type t) -> Term t -> TermM (Term t)
ctxLam Ctx.Empty        t = return t
ctxLam (Ctx.Snoc ctx _) t = ctxLam ctx =<< lam t

-- | Useful just for debugging.
extendContext
  :: (IsTerm t)
  => Ctx (Type t) -> (Name, Type t) -> TC t s (Ctx (Type t))
extendContext ctx type_ = do
  let ctx' = Ctx.Snoc ctx type_
  let msg = do
        ctxDoc <- prettyContextTC ctx'
        return $ "*** extendContext" $$ ctxDoc
  debug msg
  return ctx'

-- Monad versions of signature-requiring things
-----------------------------------------------

ctxAppTC :: (IsTerm t) => TermM (Term t) -> Ctx (Type t) -> TC t s (Term t)
ctxAppTC t ctx0 = do
  t' <- liftTermM t
  eliminateTC t' . map Apply =<< mapM varTC (ctxVars ctx0)

eliminateTC :: (IsTerm t) => t -> [Elim t] -> TC t s t
eliminateTC h els = withSignatureTermM $ \sig -> eliminate sig h els

freeVarsTC :: (IsTerm t) => t -> TC t s FreeVars
freeVarsTC t = withSignatureTermM $ \sig -> freeVars sig t

metaVarsTC :: (IsTerm t) => t -> TC t s (HS.HashSet MetaVar)
metaVarsTC t = withSignatureTermM $ \sig -> metaVars sig t

prettyTermTC :: (IsTerm t) => t -> TC t s PP.Doc
prettyTermTC t = withSignatureTermM $ \sig -> prettyTerm sig t

prettyElimsTC :: (IsTerm t) => [Elim t] -> TC t s PP.Doc
prettyElimsTC es = withSignatureTermM $ \sig -> prettyElims sig es

prettyDefinitionTC :: (IsTerm t) => Closed (Definition t) -> TC t s PP.Doc
prettyDefinitionTC def' = withSignatureTermM $ \sig -> prettyDefinition sig def'

prettyContextTC :: (IsTerm t) => Ctx.Ctx t -> TC t s PP.Doc
prettyContextTC ctx = withSignatureTermM $ \sig -> prettyContext sig ctx

unviewTC :: (IsTerm t) => TermView t -> TC t s t
unviewTC = liftTermM . unview

lamTC :: (IsTerm t) => Abs t -> TC t s t
lamTC body = liftTermM $ unview $ Lam body

piTC :: (IsTerm t) => t -> Abs t -> TC t s  t
piTC domain codomain = liftTermM $ unview $ Pi domain codomain

equalTC :: (IsTerm t) => t -> t -> t -> TC t s t
equalTC type_ x y = liftTermM $ unview $ Equal type_ x y

appTC :: (IsTerm t) => Head -> [Elim t] -> TC t s t
appTC h elims = liftTermM $ unview $ App h elims

metaVarTC :: (IsTerm t) => MetaVar -> [Elim t] -> TC t s t
metaVarTC mv = liftTermM . unview . App (Meta mv)

defTC :: (IsTerm t) => Name -> [Elim t] -> TC t s t
defTC f = liftTermM . unview . App (Def f)

conTC :: (IsTerm t) => Name -> [t] -> TC t s t
conTC c args = liftTermM $ unview (Con c args)

varTC :: (IsTerm t) => Var -> TC t s t
varTC = liftTermM . var

ctxLamTC :: (IsTerm t) => Ctx.Ctx (Type t) -> Term t -> TC t s (Term t)
ctxLamTC ctx = liftTermM . ctxLam ctx

ctxPiTC :: (IsTerm t) => Ctx (Type t) -> Type t -> TC t s (Type t)
ctxPiTC ctx type_ = liftTermM $ ctxPi ctx type_

telPiTC :: (IsTerm t) => Tel.Tel (Type t) -> Type t -> TC t s (Type t)
telPiTC tel = ctxPiTC (Tel.unTel tel)

ignoreBlockingTC :: (IsTerm t) => Blocked t -> TC t s t
ignoreBlockingTC = liftTermM . ignoreBlocking

termEqTC :: (IsTerm t) => Term t -> Term t -> TC t s Bool
termEqTC x y = liftTermM $ termEq x y

instantiateTC :: (IsTerm t) => Term t -> Term t -> TC t s (Term t)
instantiateTC x y = liftTermM $ instantiate x y

-- Miscellanea
--------------

isApply :: Elim (Term t) -> Maybe (Term t)
isApply (Apply v) = Just v
isApply Proj{}    = Nothing

definitionType :: (IsTerm t) => Closed (Definition t) -> TC t s (Closed (Type t))
definitionType (Constant _ type_)         = return type_
definitionType (DataCon _ _ tel type_)    = telPiTC tel type_
definitionType (Projection _ _ tel type_) = telPiTC tel type_
definitionType (Function type_ _)         = return type_

isRecordType :: (IsTerm t) => Name -> TC t s Bool
isRecordType tyCon = withSignature $ \sig ->
  case Sig.getDefinition sig tyCon of
    Constant (Record _ _) _ -> True
    _                       -> False

isRecordConstr :: (IsTerm t) => Name -> TC t s Bool
isRecordConstr dataCon = join $ withSignature $ \sig ->
  case Sig.getDefinition sig dataCon of
    DataCon tyCon _ _ _ -> isRecordType tyCon
    _                   -> return False

getAbsNameTC
  :: (IsTerm t) => Abs (Term t) -> TC t s Name
getAbsNameTC t = do
  -- TODO introduce configuration
  -- fast <- tcsFastGetAbsName <$> getState
  let fast = False
  if fast
    then return "_"
    else liftTermM $ getAbsName_ t

headType
  :: (IsTerm t)
  => Ctx t -> Head -> TC t s (Type t)
headType ctx h = case h of
  Var v   -> liftTermM $ Ctx.getVar v ctx
  Def f   -> definitionType =<< getDefinition f
  J       -> return typeOfJ
  Meta mv -> getMetaVarType mv

-- Unrolling Pis
----------------

-- TODO remove duplication

unrollPiWithNames
  :: (IsTerm t)
  => Type t
  -- ^ Type to unroll
  -> [Name]
  -- ^ Names to give to each parameter
  -> TC t s (Ctx (Type t), Type t)
  -- ^ A telescope with accumulated domains of the pis and the final
  -- codomain.
unrollPiWithNames type_ [] =
  return (Ctx.Empty, type_)
unrollPiWithNames type_ (name : names) = do
  typeView <- whnfViewTC type_
  case typeView of
    Pi domain codomain -> do
      (ctx, endType) <- unrollPiWithNames codomain names
      return (Ctx.singleton name domain Ctx.++ ctx, endType)
    _ -> do
      checkError $ ExpectingPi type_

unrollPi
  :: (IsTerm t)
  => Type t
  -- ^ Type to unroll
  -> TC t s (Ctx (Type t), Type t)
unrollPi type_ = do
  typeView <- whnfViewTC type_
  case typeView of
    Pi domain codomain -> do
      name <- getAbsNameTC codomain
      (ctx, endType) <- unrollPi codomain
      return (Ctx.singleton name domain Ctx.++ ctx, endType)
    _ ->
      return (Ctx.Empty, type_)

-- Constraints
--------------

data Constraint t
  = Unify (Ctx t) (Type t) (Term t) (Term t)
  | Conj [Constraint t]
  | (:>>:) (Constraint t) (Constraint t)

instance Monoid (Constraint t) where
  mempty = Conj []

  Conj cs1 `mappend` Conj cs2 = Conj (cs1 ++ cs2)
  Conj cs1 `mappend` c2       = Conj (c2 : cs1)
  c1       `mappend` Conj cs2 = Conj (c1 : cs2)
  c1       `mappend` c2       = Conj [c1, c2]

-- Pretty printing Constraints

prettyConstraintTC
  :: (IsTerm t) => Constraint t -> TC t s PP.Doc
prettyConstraintTC c = case c of
  Unify ctx type_ t1 t2 -> do
    ctxDoc <- prettyContextTC ctx
    typeDoc <- prettyTermTC type_
    t1Doc <- prettyTermTC t1
    t2Doc <- prettyTermTC t2
    return $ group $
      ctxDoc <+> "|-" //
      group (t1Doc // hang 2 "=" // t2Doc // hang 2 ":" // typeDoc)
  c1 :>>: c2 -> do
    c1Doc <- prettyConstraintTC c1
    c2Doc <- prettyConstraintTC c2
    return $ group (group c1Doc $$ hang 2 ">>" $$ group c2Doc)
  Conj cs -> do
    csDoc <- mapM prettyConstraintTC cs
    return $
      "Conj" //> PP.list csDoc

-- Clauses invertibility
------------------------

termHead :: (IsTerm t) => t -> TC t s (Maybe TermHead)
termHead t = do
  tView <- whnfViewTC t
  case tView of
    App (Def f) _ -> do
      fDef <- getDefinition f
      return $ case fDef of
        Constant Data{}      _ -> Just $ DefHead f
        Constant Record{}    _ -> Just $ DefHead f
        -- TODO here we can't return 'Just' because we don't know if the
        -- postulate is going to be instantiated afterwards.  Ideally we'd
        -- have a "postulate" keyword to avoid this.
        Constant Postulate{} _ -> Nothing
        _                      -> Nothing
    Con f _ ->
      return $ Just $ DefHead f
    Pi _ _ ->
      return $ Just $ PiHead
    _ ->
      return $ Nothing

checkInvertibility
  :: (IsTerm t) => [Closed (Clause t)] -> TC t s (Closed (Invertible t))
checkInvertibility = go []
  where
    go injClauses [] =
      return $ Invertible $ reverse injClauses
    go injClauses (clause@(Clause _ body) : clauses) = do
      th <- termHead body
      case th of
        Just tHead | Nothing <- lookup tHead injClauses ->
          go ((tHead, clause) : injClauses) clauses
        _ ->
          return $ NotInvertible $ reverse (map snd injClauses) ++ (clause : clauses)
