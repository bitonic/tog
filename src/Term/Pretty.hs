{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Term.Pretty
  ( prettyTerm
  , prettyElim
  , prettyElims
  , prettyDefinition
  , prettyClause
  , prettyTelWithTerm
  , prettyTel
  , prettyContext
  ) where

import           Prelude.Extended
import           PrettyPrint                      ((<+>), ($$), (</>), (//>), ($$>))
import qualified PrettyPrint                      as PP
import qualified Syntax.Internal                  as A
import           Term.Class
import qualified Term.Context                     as Ctx
import qualified Term.Signature                   as Sig
import           Term.Synonyms
import qualified Term.Telescope                   as Tel
import           Term.TermM
import           Term.Utils

prettyTerm :: (IsTerm t) => Sig.Signature t -> t -> TermM PP.Doc
prettyTerm sig = prettyPrecTerm sig 0

prettyPrecTerm :: (IsTerm t) => Sig.Signature t -> Int -> t -> TermM PP.Doc
prettyPrecTerm sig p t0 = do
  synT <- internalToTerm =<< instantiateMetaVars sig t0
  return $ PP.prettyPrec p synT

prettyElim :: (IsTerm t) => Sig.Signature t -> Elim t -> TermM PP.Doc
prettyElim _   (Proj n _) = return $ PP.pretty $ A.Proj n
prettyElim sig (Apply t)  = PP.pretty . A.Apply <$> (internalToTerm =<< instantiateMetaVars sig t)

prettyElims :: (IsTerm t) => Sig.Signature t -> [Elim t] -> TermM PP.Doc
prettyElims sig elims = PP.pretty <$> mapM (prettyElim sig) elims

prettyDefinition :: (IsTerm t) => Sig.Signature t -> Closed (Definition t) -> TermM PP.Doc
prettyDefinition sig (Constant Postulate type_) =
  prettyTerm sig type_
prettyDefinition sig (Constant (Data dataCons) type_) = do
  typeDoc <- prettyTerm sig type_
  return $ "data" <+> typeDoc <+> "where" $$>
           PP.vcat (map PP.pretty dataCons)
prettyDefinition sig (Constant (Record dataCon fields) type_) = do
  typeDoc <- prettyTerm sig type_
  return $ "record" <+> typeDoc <+> "where" $$>
           "constructor" <+> PP.pretty dataCon $$
           "field" $$>
           PP.vcat (map (PP.pretty . fst) fields)
prettyDefinition sig (DataCon tyCon pars type_) = do
  typeDoc <- prettyTelWithTerm sig pars type_
  return $ "constructor" <+> PP.pretty tyCon $$> typeDoc
prettyDefinition sig (Projection _ tyCon pars type_) = do
  typeDoc <- prettyTelWithTerm sig pars type_
  return $ "projection" <+> PP.pretty tyCon $$> typeDoc
prettyDefinition sig (Function type_ clauses) = do
  typeDoc <- prettyTerm sig type_
  clausesDoc <- mapM (prettyClause sig) $ ignoreInvertible clauses
  return $ typeDoc $$ PP.vcat clausesDoc

prettyClause :: (IsTerm t) => Sig.Signature t -> Closed (Clause t) -> TermM PP.Doc
prettyClause sig (Clause pats body) = do
  bodyDoc <- prettyTerm sig body
  return $ PP.group $
    PP.hsep (map PP.pretty pats ++ ["="]) //> bodyDoc

prettyTel
  :: (IsTerm t)
  => Sig.Signature t -> Tel.Tel t -> TermM PP.Doc
prettyTel _ Tel.Empty = do
  return "[]"
prettyTel sig (Tel.Cons (n0, type0) tel0) = do
  type0Doc <- prettyTerm sig type0
  tel0Doc <- go tel0
  return $ "[" <+> PP.pretty n0 <+> ":" <+> type0Doc </> tel0Doc
  where
    go Tel.Empty =
      return "]"
    go (Tel.Cons (n, type_) tel) = do
      typeDoc <- prettyTerm sig type_
      telDoc <- go tel
      return $ ";" <+> PP.pretty n <+> ":" <+> typeDoc <+> telDoc

prettyTelWithTerm
  :: (IsTerm t)
  => Sig.Signature t -> Tel.Tel t -> t -> TermM PP.Doc
prettyTelWithTerm sig Tel.Empty t =
  prettyTerm sig t
prettyTelWithTerm sig tel t =
  (</>) <$> prettyTel sig tel <*> prettyTerm sig t

prettyContext
  :: (IsTerm t)
  => Sig.Signature t -> Ctx.Ctx t -> TermM PP.Doc
prettyContext sig = prettyTel sig . Tel.tel

-- Instances
------------------------------------------------------------------------

instance PP.Pretty Pattern where
  pretty e = case e of
    VarP      -> PP.text "_"
    ConP c es -> prettyApp 10 (PP.pretty c) es

prettyApp :: PP.Pretty a => Int -> PP.Doc -> [a] -> PP.Doc
prettyApp _ h []   = h
prettyApp p h args = PP.condParens (p > 3) $ h </> PP.fillSep (map (PP.prettyPrec 4) args)

