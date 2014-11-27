{-# LANGUAGE OverloadedStrings #-}
module TypeCheck3.Common
  ( -- * Errors
    CheckError(..)
  , checkError
    -- * Constraints
  , Constraint(..)
  , Constraints
  , jmEq
    -- * Clauses invertibility
  , termHead
  , checkInvertibility
    -- * Miscellanea
  , addMetaInCtx
  , extendContext
  , unrollPiWithNames
  , unrollPi
  ) where

import           Prelude                          hiding (abs, pi)

import           Instrumentation
import           Prelude.Extended
import           Syntax
import qualified Syntax.Abstract                  as SA
import           Term
import           PrettyPrint                      (($$), (<+>), (//>))
import qualified PrettyPrint                      as PP
import           TypeCheck3.Monad

-- Errors
---------

data CheckError t
    = ExpectingEqual (Type t)
    | ExpectingPi (Type t)
    | ExpectingTyCon (Opened Name t) (Type t)
    | FreeVariableInEquatedTerm Meta [Elim t] (Term t) Var
    | NameNotInScope Name
    | OccursCheckFailed Meta (Closed (Term t))
    | SpineNotEqual (Type t) [Elim t] (Type t) [Elim t]
    | TermsNotEqual (Type t) (Term t) (Type t) (Term t)
    | PatternMatchOnRecord SA.Pattern (Opened Name t) -- Record type constructor

checkError :: (IsTerm t) => CheckError t -> TC t s a
checkError err = typeError =<< renderError err

renderError :: (IsTerm t) => CheckError t -> TC t s PP.Doc
renderError err =
  case err of
    TermsNotEqual type1 t1 type2 t2 -> do
      t1Doc <- prettyM t1
      type1Doc <- prettyM type1
      t2Doc <- prettyM t2
      type2Doc <- prettyM type2
      return $
        "Terms not equal:" $$
        "t:" //> t1Doc $$
        "A:" //> type1Doc $$
        "u:" //> t2Doc $$
        "B:" //> type2Doc
    SpineNotEqual type1 es1 type2 es2 -> do
      type1Doc <- prettyM type1
      es1Doc <- PP.list <$> mapM prettyM es1
      type2Doc <- prettyM type2
      es2Doc <- PP.list <$> mapM prettyM es2
      return $
        "Spines not equal:" $$
        "es:" //> es1Doc $$
        "A:" //> type1Doc $$
        "ds:" //> es2Doc $$
        "B:" //> type2Doc
    FreeVariableInEquatedTerm mv els rhs v -> do
      mvDoc <- prettyM =<< meta mv els
      rhsDoc <- prettyM rhs
      return $ "Free variable `" <> prettyVar v <> "' in term equated to metavariable application:" $$
               mvDoc $$ PP.nest 2 "=" $$ rhsDoc
    OccursCheckFailed mv t -> do
      tDoc <- prettyM t
      return $ "Attempt at recursive instantiation:" $$ PP.pretty mv <+> ":=" <+> tDoc
    NameNotInScope name -> do
      return $ "Name not in scope:" <+> PP.pretty name
    PatternMatchOnRecord synPat tyCon -> do
      tyConDoc <- prettyM tyCon
      return $ "Cannot have pattern" <+> PP.pretty synPat <+> "for record type" <+> tyConDoc
    ExpectingPi type_ -> do
      typeDoc <- prettyM type_
      return $ "Expecting a pi type, not:" //> typeDoc
    ExpectingEqual type_ -> do
      typeDoc <- prettyM type_
      return $ "Expecting an identity type, not:" //> typeDoc
    ExpectingTyCon tyCon type_ -> do
      tyConDoc <- prettyM tyCon
      typeDoc <- prettyM type_
      return $ "Expecting a" <+> tyConDoc <> ", not:" //> typeDoc
  where
    prettyVar = PP.pretty


-- Meta handling
------------------------------------------------------------------------

addMetaInCtx
  :: (IsTerm t)
  => Ctx t -> Type t -> TC t s (Term t)
addMetaInCtx ctx type_ = do
  type' <- ctxPi ctx type_
  mv <- addMeta type'
  ctxApp (meta mv []) ctx

-- Telescope & context utils
----------------------------

-- | Useful just for debugging.
extendContext
  :: (IsTerm t)
  => Ctx (Type t) -> (Name, Type t) -> TC t s (Ctx (Type t))
extendContext ctx type_ = do
  let ctx' = ctx :< type_
  debug "extendContext" $ prettyM ctx'
  return ctx'

-- Unrolling Pis
----------------

-- TODO remove duplication

unrollPiWithNames
  :: (IsTerm t)
  => Type t
  -- ^ Type to unroll
  -> [Name]
  -- ^ Names to give to each parameter
  -> TC t s (Tel (Type t), Type t)
  -- ^ A telescope with accumulated domains of the pis and the final
  -- codomain.
unrollPiWithNames type_ [] =
  return (T0, type_)
unrollPiWithNames type_ (name : names) = do
  typeView <- whnfView type_
  case typeView of
    Pi domain codomain -> do
      (ctx, endType) <- unrollPiWithNames codomain names
      return ((name, domain) :> ctx, endType)
    _ -> do
      checkError $ ExpectingPi type_

unrollPi
  :: (IsTerm t)
  => Type t
  -- ^ Type to unroll
  -> TC t s (Tel (Type t), Type t)
unrollPi type_ = do
  typeView <- whnfView type_
  case typeView of
    Pi domain codomain -> do
      name <- getAbsName_ codomain
      (ctx, endType) <- unrollPi codomain
      return ((name, domain) :> ctx, endType)
    _ ->
      return (T0, type_)

-- Constraints
--------------

type Constraints t = [Constraint t]

data Constraint t
  = JmEq (Ctx t)
         (Type t) (Term t)
         (Type t) (Term t)

jmEq :: Ctx t -> Type t -> Term t -> Type t -> Term t -> Constraints t
jmEq ctx type1 t1 type2 t2 = [JmEq ctx type1 t1 type2 t2]

instance PrettyM t (Constraint t) where
  prettyM c = case c of
    JmEq ctx type1 t1 type2 t2 -> do
      ctxDoc <- prettyM ctx
      type1Doc <- prettyM type1
      t1Doc <- prettyM t1
      type2Doc <- prettyM type2
      t2Doc <- prettyM t2
      return $
        "JmEq" $$
        "ctx:" //> ctxDoc $$
        "t:" //> t1Doc $$
        "A:" //> type1Doc $$
        "u:" //> t2Doc $$
        "B:" //> type2Doc

-- Clauses invertibility
------------------------

termHead :: (IsTerm t) => t -> TC t s (Maybe TermHead)
termHead t = do
  tView <- whnfView t
  case tView of
    App (Def opnd) _ -> do
      let f = opndKey opnd
      fDef <- getDefinition opnd
      return $ case fDef of
        Constant _ Data{}      -> Just $ DefHead f
        Constant _ Record{}    -> Just $ DefHead f
        Constant _ Postulate{} -> Just $ DefHead f
        Constant _ Function{}  -> Nothing
        DataCon{}              -> Nothing
        Projection{}           -> Nothing
    App{} -> do
      return Nothing
    Con f _ ->
      return $ Just $ DefHead $ opndKey f
    Pi{} ->
      return $ Just $ PiHead
    Lam{} ->
      return Nothing
    Refl{} ->
      return Nothing
    Set{} ->
      return Nothing
    Equal{} ->
      return Nothing

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
