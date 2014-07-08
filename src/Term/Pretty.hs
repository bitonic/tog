{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Term.Pretty
  ( prettyTerm
  , prettyElim
  , prettyElims
  , prettyDefinition
  , prettyClause
  , prettyTele
  ) where

import           Control.Applicative              ((<$>))

import           Term.Class
import           Term.Definition
import qualified Term.Signature                   as Sig
import           Term.Synonyms
import           Term.TermM
import qualified Term.Telescope                   as Tel
import           Term.Var
import           Text.PrettyPrint.Extended        ((<+>), (<>), ($$))
import qualified Text.PrettyPrint.Extended        as PP

prettyTerm :: (IsTerm t) => Sig.Signature t -> t v -> TermM PP.Doc
prettyTerm sig = prettyPrecTerm sig 0

prettyPrecTerm :: (IsTerm t) => Sig.Signature t -> Int -> t v -> TermM PP.Doc
prettyPrecTerm sig p t0 = do
  t <- view =<< instantiateMetaVars sig t0
  case t of
    Set ->
      return $ PP.text "Set"
    Equal a x y ->
      prettyApp (prettyPrecTerm sig) p (PP.text "_==_") [a, x, y]
    Pi a b -> do
      mbN <- getAbsName b
      aDoc <- prettyTerm sig a
      bDoc <- prettyTerm sig b
      return $ PP.condParens (p > 0) $
          PP.sep [ (PP.parens $ case mbN of
                      Nothing -> aDoc
                      Just n  -> PP.pretty n <> PP.text " : " <> aDoc) PP.<+>
                   PP.text "->"
                 , PP.nest 2 bDoc
                 ]
    Lam b -> do
      n <- getAbsName_ b
      bDoc <- prettyTerm sig b
      return $ PP.condParens (p > 0) $
         PP.sep [ PP.text "\\" <> PP.pretty n <> PP.text " ->"
                , PP.nest 2 bDoc
                ]
    App h es ->
      prettyApp (prettyPrecElim sig) p (PP.pretty h) es
    Refl ->
      return $ PP.text "refl"
    Con dataCon args ->
      prettyApp (prettyPrecTerm sig) p (PP.pretty dataCon) args

prettyApp :: (Int -> a -> TermM PP.Doc) -> Int -> PP.Doc -> [a] -> TermM (PP.Doc)
prettyApp _f _p h [] = return h
prettyApp f   p h xs = do
  xsDoc <- mapM (f 4) xs
  return $ PP.condParens (p > 3) $ h <+> PP.fsep xsDoc

prettyElim :: (IsTerm t) => Sig.Signature t -> Elim t v -> TermM PP.Doc
prettyElim sig = prettyPrecElim sig 0

prettyPrecElim :: (IsTerm t) => Sig.Signature t -> Int -> Elim t v -> TermM PP.Doc
prettyPrecElim p sig (Apply e)  = prettyPrecTerm p sig e
prettyPrecElim _ _   (Proj n _) = return $ PP.text $ show n

prettyElims :: (IsTerm t) => Sig.Signature t -> [Elim t v] -> TermM PP.Doc
prettyElims sig elims = PP.pretty <$> mapM (prettyElim sig) elims

prettyDefinition :: (IsTerm t) => Sig.Signature t -> Closed (Definition t) -> TermM PP.Doc
prettyDefinition sig (Constant Postulate type_) =
  prettyTerm sig type_
prettyDefinition sig (Constant (Data dataCons) type_) = do
  typeDoc <- prettyTerm sig type_
  return $ "data" <+> typeDoc <+> "where" $$
           PP.nest 2 (PP.vcat (map PP.pretty dataCons))
prettyDefinition sig (Constant (Record dataCon fields) type_) = do
  typeDoc <- prettyTerm sig type_
  return $ "record" <+> typeDoc <+> "where" $$
           PP.nest 2 ("constructor" <+> PP.pretty dataCon) $$
           PP.nest 2 ("field" $$ PP.nest 2 (PP.vcat (map (PP.pretty . fst) fields)))
prettyDefinition sig (DataCon tyCon type_) = do
  typeDoc <- prettyTele sig type_
  return $ "constructor" <+> PP.pretty tyCon $$ PP.nest 2 typeDoc
prettyDefinition sig (Projection _ tyCon type_) = do
  typeDoc <- prettyTele sig type_
  return $ "projection" <+> PP.pretty tyCon $$ PP.nest 2 typeDoc
prettyDefinition sig (Function type_ clauses) = do
  typeDoc <- prettyTerm sig type_
  clausesDoc <- mapM (prettyClause sig) $ ignoreInvertible clauses
  return $ typeDoc $$ PP.vcat clausesDoc

prettyClause :: (IsTerm t) => Sig.Signature t -> Closed (Clause t) -> TermM PP.Doc
prettyClause sig (Clause pats body) = do
  bodyDoc <- prettyClauseBody sig body
  return $ PP.pretty pats <+> "=" $$ PP.nest 2 bodyDoc

prettyClauseBody :: (IsTerm t) => Sig.Signature t -> ClauseBody t v -> TermM PP.Doc
prettyClauseBody sig (CBNil t) = prettyTerm sig t
prettyClauseBody sig (CBArg t) = prettyClauseBody sig t

prettyTele
  :: forall v t. (IsTerm t)
  => Sig.Signature t -> Tel.IdTel t v -> TermM PP.Doc
prettyTele sig (Tel.Empty (Tel.Id t)) = do
   prettyTerm sig t
prettyTele sig (Tel.Cons (n0, type0) tel0) = do
  type0Doc <- prettyTerm sig type0
  tel0Doc <- go tel0
  return $ "[" <+> PP.pretty n0 <+> ":" <+> type0Doc PP.<> tel0Doc
  where
    go :: forall v'. Tel.IdTel t v' -> TermM PP.Doc
    go (Tel.Empty (Tel.Id t)) =
      ("]" <+>) <$> prettyTerm sig t
    go (Tel.Cons (n, type_) tel) = do
      typeDoc <- prettyTerm sig type_
      telDoc <- go tel
      return $ ";" <+> PP.pretty n <+> ":" <+> typeDoc <+> telDoc

-- Instances
------------------------------------------------------------------------

instance PP.Pretty (Head v) where
    pretty (Var v)   = PP.pretty (varIndex v) <> "#" <> PP.pretty (varName v)
    pretty (Def f)   = PP.pretty f
    pretty J         = PP.text "J"
    pretty (Meta mv) = PP.pretty mv

instance PP.Pretty Pattern where
  prettyPrec p e = case e of
    VarP      -> PP.text "_"
    ConP c es -> PP.prettyApp p (PP.pretty c) es
