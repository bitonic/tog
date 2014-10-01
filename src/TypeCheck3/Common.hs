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
      t1Doc <- prettyTermM t1
      type1Doc <- prettyTermM type1
      t2Doc <- prettyTermM t2
      type2Doc <- prettyTermM type2
      return $
        t1Doc <+> ":" <+> type1Doc $$
        PP.nest 2 "!=" $$
        t2Doc <+> ":" <+> type2Doc
    SpineNotEqual type1 es1 type2 es2 -> do
      type1Doc <- prettyTermM type1
      es1Doc <- PP.list <$> mapM prettyM es1
      type2Doc <- prettyTermM type2
      es2Doc <- PP.list <$> mapM prettyM es2
      return $
        es1Doc <+> ":" <+> type1Doc $$
        PP.nest 2 "!=" $$
        es2Doc <+> ":" <+> type2Doc
    FreeVariableInEquatedTerm mv els rhs v -> do
      mvDoc <- prettyTermM =<< metaVar mv els
      rhsDoc <- prettyTermM rhs
      return $ "Free variable `" PP.<> prettyVar v PP.<> "' in term equated to metavariable application:" $$
               mvDoc $$ PP.nest 2 "=" $$ rhsDoc
    OccursCheckFailed mv t -> do
      tDoc <- prettyTermM t
      return $ "Attempt at recursive instantiation:" $$ PP.pretty mv <+> ":=" <+> tDoc
    NameNotInScope name -> do
      return $ "Name not in scope:" <+> PP.pretty name
    PatternMatchOnRecord synPat tyCon -> do
      return $ "Cannot have pattern" <+> PP.pretty synPat <+> "for record type" <+> PP.pretty tyCon
    ExpectingPi type_ -> do
      typeDoc <- prettyTermM type_
      return $ "Expecting a pi type, not:" //> typeDoc
    ExpectingEqual type_ -> do
      typeDoc <- prettyTermM type_
      return $ "Expecting an identity type, not:" //> typeDoc
    ExpectingTyCon tyCon type_ -> do
      typeDoc <- prettyTermM type_
      return $ "Expecting a" <+> PP.pretty tyCon PP.<> ", not:" //> typeDoc
  where
    prettyVar = PP.pretty


-- MetaVar handling
------------------------------------------------------------------------

addMetaVarInCtx
  :: (IsTerm t)
  => Ctx t -> Type t -> TC t s (Term t)
addMetaVarInCtx ctx type_ = do
  mv <- addMetaVar =<< ctxPi ctx type_
  ctxApp (metaVar mv []) ctx

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
ctxPi :: (IsTerm t, MonadTerm t m) => Ctx (Type t) -> Type t -> m (Type t)
ctxPi Ctx.Empty                  t = return t
ctxPi (Ctx.Snoc ctx (_n, type_)) t = ctxPi ctx =<< pi type_ t

-- | Creates a 'Lam' term with as many arguments there are in the
-- 'Ctx.Ctx'.
ctxLam :: (IsTerm t, MonadTerm t m) => Ctx (Type t) -> Term t -> m (Term t)
ctxLam Ctx.Empty        t = return t
ctxLam (Ctx.Snoc ctx _) t = ctxLam ctx =<< lam t

-- | Useful just for debugging.
extendContext
  :: (IsTerm t)
  => Ctx (Type t) -> (Name, Type t) -> TC t s (Ctx (Type t))
extendContext ctx type_ = do
  let ctx' = Ctx.Snoc ctx type_
  let msg = do
        ctxDoc <- prettyM ctx'
        return $ "*** extendContext" $$ ctxDoc
  debug msg
  return ctx'

-- Monad versions of signature-requiring things
-----------------------------------------------

ctxApp :: (IsTerm t, MonadTerm t m) => m (Term t) -> Ctx (Type t) -> m (Term t)
ctxApp t ctx0 = do
  t' <- t
  eliminate t' . map Apply =<< mapM var (ctxVars ctx0)

telPi :: (IsTerm t) => Tel.Tel (Type t) -> Type t -> TC t s (Type t)
telPi = ctxPi . Tel.unTel

-- Miscellanea
--------------

isApply :: Elim (Term t) -> Maybe (Term t)
isApply (Apply v) = Just v
isApply Proj{}    = Nothing

definitionType :: (IsTerm t) => Closed (Definition t) -> TC t s (Closed (Type t))
definitionType (Constant _ type_)         = return type_
definitionType (DataCon _ _ tel type_)    = telPi tel type_
definitionType (Projection _ _ tel type_) = telPi tel type_
definitionType (Function type_ _)         = return type_

isRecordType :: (IsTerm t) => Name -> TC t s Bool
isRecordType tyCon = do
  sig <- askSignature
  return $ case Sig.getDefinition sig tyCon of
    Constant (Record _ _) _ -> True
    _                       -> False

isRecordConstr :: (IsTerm t) => Name -> TC t s Bool
isRecordConstr dataCon = do
  sig <- askSignature
  case Sig.getDefinition sig dataCon of
    DataCon tyCon _ _ _ -> isRecordType tyCon
    _                   -> return False

headType
  :: (IsTerm t)
  => Ctx t -> Head -> TC t s (Type t)
headType ctx h = case h of
  Var v   -> Ctx.getVar v ctx
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
  typeView <- whnfView type_
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
  typeView <- whnfView type_
  case typeView of
    Pi domain codomain -> do
      name <- getAbsName_ codomain
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

instance PrettyM Constraint where
  prettyM c = case c of
    Unify ctx type_ t1 t2 -> do
      ctxDoc <- prettyM ctx
      typeDoc <- prettyTermM type_
      t1Doc <- prettyTermM t1
      t2Doc <- prettyTermM t2
      return $ group $
        ctxDoc <+> "|-" //
        group (t1Doc // hang 2 "=" // t2Doc // hang 2 ":" // typeDoc)
    c1 :>>: c2 -> do
      c1Doc <- prettyM c1
      c2Doc <- prettyM c2
      return $ group (group c1Doc $$ hang 2 ">>" $$ group c2Doc)
    Conj cs -> do
      csDoc <- mapM prettyM cs
      return $
        "Conj" //> PP.list csDoc

-- Clauses invertibility
------------------------

termHead :: (IsTerm t) => t -> TC t s (Maybe TermHead)
termHead t = do
  tView <- whnfView t
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
