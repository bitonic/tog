{-# LANGUAGE OverloadedStrings #-}
-- | Common error type for elaboration/unification/checking
module Error
  ( CheckError(..)
  ) where

import           Prelude                          hiding (abs, pi)
import qualified Data.HashSet                     as HS

import           TogPrelude
import           Names
import qualified Abstract                         as SA
import           Term
import           PrettyPrint                      (($$), (<+>), (//>))
import qualified PrettyPrint                      as PP

-- Errors
---------

data CheckError t
    = ExpectingEqual (Type t)
    | ExpectingPi (Type t)
    | ExpectingTyCon QName (Type t)
    | FreeVariableInEquatedTerm Meta [Elim t] (Term t) Var
    | OccursCheckFailed Meta (Closed (Term t))
    | SpineNotEqual (Type t) [Elim t] (Type t) [Elim t]
    | TermsNotEqual (Type t) (Term t) (Type t) (Term t)
    | PatternMatchOnRecord SA.Pattern QName -- Record type constructor
    | MismatchingArgumentsForModule QName (Tel t) [SA.Expr]
    | UnsolvedMetas MetaSet

instance PrettyM t (CheckError t) where
  prettyM err =
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
      UnsolvedMetas mvs -> do
        return $ "UnsolvedMetas" <+> PP.pretty (HS.toList mvs)
      MismatchingArgumentsForModule n tel args -> do
        telDoc <- prettyM tel
        return $
          "MismatchingArgumentsForModule" $$
          "module:" //> PP.pretty n $$
          "tel:" //> telDoc $$
          "args:" //> PP.hsep (map PP.pretty args)
    where
      prettyVar = PP.pretty
