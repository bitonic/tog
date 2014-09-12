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

import           Conf
import           Prelude.Extended                 hiding ((<>))
import           PrettyPrint                      ((<+>), ($$), (</>), (//>), ($$>), (<>))
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
  normalize <- confNormalizePrettyPrinted <$> readConf
  t <- if normalize then nf sig t0 else return t0
  synT <- internalToTerm t
  return $ PP.prettyPrec p synT

prettyElim :: (IsTerm t) => Sig.Signature t -> Elim t -> TermM PP.Doc
prettyElim _   (Proj n _) = return $ PP.pretty $ A.Proj n
prettyElim sig (Apply t)  = PP.pretty . A.Apply <$> (internalToTerm =<< instantiateMetaVars sig t)

prettyElims :: (IsTerm t) => Sig.Signature t -> [Elim t] -> TermM PP.Doc
prettyElims sig elims =
  PP.list <$> mapM (prettyElim sig) elims

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
prettyTel sig tel00 = fmap PP.group $ case tel00 of
  Tel.Empty -> do
    return "[]"
  Tel.Cons (n0, type0) tel0 -> do
    type0Doc <- prettyTerm sig type0
    tel0Doc <- go tel0
    return $ "[" <+> PP.pretty n0 <+> ":" <+> type0Doc <> PP.linebreak <> tel0Doc
  where
    go Tel.Empty = do
      return "]"
    go (Tel.Cons (n, type_) tel) = do
      typeDoc <- prettyTerm sig type_
      telDoc <- go tel
      return $ ";" <+> PP.pretty n <+> ":" <+> typeDoc <> PP.linebreak <> telDoc

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



-- To A.Expr
------------------------------------------------------------------------

internalToTerm
  :: (IsTerm t) => t -> TermM A.Expr
internalToTerm t0 = do
  tView <- view t0
  case tView of
    Lam body -> do
      n <- getAbsName_ body
      A.Lam n <$> internalToTerm body
    Pi dom cod -> do
      mbCod <- strengthen_ 1 cod
      case mbCod of
        Nothing -> do
          n <- getAbsName_ cod
          A.Pi n <$> internalToTerm dom <*> internalToTerm cod
        Just cod' -> do
          A.Fun <$> internalToTerm dom <*> internalToTerm cod'
    Equal type_ x y ->
      A.Equal <$> internalToTerm type_ <*> internalToTerm x <*> internalToTerm y
    Refl ->
      return $ A.Refl A.noSrcLoc
    Con dataCon args ->
      A.Con dataCon <$> mapM internalToTerm args
    Set ->
      return $ A.Set A.noSrcLoc
    App h args -> do
      let h' = case h of
            Var v -> A.Var (A.name (PP.render v))
            Def f -> A.Def f
            J -> A.J A.noSrcLoc
            Meta mv -> A.Var (A.Name (A.srcLoc mv) (PP.render mv))
      A.App h' <$> mapM (foldElim (\t -> A.Apply <$> internalToTerm t) (\n _ -> return $ A.Proj n)) args
