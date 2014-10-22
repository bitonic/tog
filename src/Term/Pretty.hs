{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Term.Pretty
  ( prettyTermM
  , prettyArgM
  , PrettyM(prettyM)
  , prettyListM
  ) where

import           Conf
import           Prelude.Extended                 hiding ((<>))
import           PrettyPrint                      ((<+>), ($$), (</>), (//>), ($$>), (<>))
import qualified PrettyPrint                      as PP
import qualified Syntax.Internal                  as SI
import           Term.Types
import qualified Term.Context                     as Ctx
import qualified Term.Telescope                   as Tel
import           Term.MonadTerm

prettyTermM :: (IsTerm t, MonadTerm t m) => t -> m PP.Doc
prettyTermM = prettyPrecTermM 0

prettyPrecTermM :: (IsTerm t, MonadTerm t m) => Int -> t -> m PP.Doc
prettyPrecTermM p t = do
  synT <- internalToTerm t
  return $ PP.prettyPrec p synT

prettyArgM :: (IsTerm t, MonadTerm t m) => t -> m PP.Doc
prettyArgM = prettyPrecTermM 4

class PrettyM f where
  prettyM :: (IsTerm t, MonadTerm t m) => f t -> m PP.Doc

instance PrettyM Elim where
  prettyM (Proj p)  = return $ PP.pretty $ SI.Proj $ pName p
  prettyM (Apply t) = PP.pretty . SI.Apply <$> internalToTerm t

instance PrettyM Definition where
  prettyM (Constant Postulate type_) = do
    typeDoc <- prettyTermM type_
    return $ "postulate" //> typeDoc
  prettyM (Constant TypeSig type_) = do
    prettyTermM type_
  prettyM (Constant (Data dataCons) type_) = do
    typeDoc <- prettyTermM type_
    return $ "data" <+> typeDoc <+> "where" $$>
             PP.vcat (map PP.pretty dataCons)
  prettyM (Constant (Record dataCon fields) type_) = do
    typeDoc <- prettyTermM type_
    return $ "record" <+> typeDoc <+> "where" $$>
             "constructor" <+> PP.pretty dataCon $$
             "field" $$>
             PP.vcat (map (PP.pretty . pName) fields)
  prettyM (DataCon tyCon _ pars type_) = do
    typeDoc <- prettyTelWithTerm pars type_
    return $ "constructor" <+> PP.pretty tyCon $$> typeDoc
  prettyM (Projection _ tyCon pars type_) = do
    typeDoc <- prettyTelWithTerm pars type_
    return $ "projection" <+> PP.pretty tyCon $$> typeDoc
  prettyM (Function type_ clauses) = do
    typeDoc <- prettyTermM type_
    clausesDoc <- mapM prettyM $ ignoreInvertible clauses
    return $ typeDoc $$ PP.vcat clausesDoc

instance PrettyM Clause where
  prettyM (Clause pats body) = do
    bodyDoc <- prettyTermM body
    return $ PP.group $
      PP.hsep (map PP.pretty pats ++ ["="]) //> bodyDoc

instance PrettyM Tel.Tel where
  prettyM tel00 = fmap PP.group $ case tel00 of
    Tel.Empty -> do
      return "[]"
    Tel.Cons (n0, type0) tel0 -> do
      type0Doc <- prettyTermM type0
      tel0Doc <- go tel0
      return $ "[" <+> PP.pretty n0 <+> ":" <+> type0Doc <> PP.linebreak <> tel0Doc
    where
      go Tel.Empty = do
        return "]"
      go (Tel.Cons (n, type_) tel) = do
        typeDoc <- prettyTermM type_
        telDoc <- go tel
        return $ ";" <+> PP.pretty n <+> ":" <+> typeDoc <> PP.linebreak <> telDoc

prettyTelWithTerm
  :: (IsTerm t, MonadTerm t m)
  => Tel.Tel t -> t -> m PP.Doc
prettyTelWithTerm Tel.Empty t =
  prettyTermM t
prettyTelWithTerm tel t =
  (</>) <$> prettyM tel <*> prettyTermM t

instance PrettyM Ctx.Ctx where
  prettyM = prettyM . Tel.tel

prettyListM
  :: (IsTerm t, PrettyM f, MonadTerm t m) => [f t] -> m PP.Doc
prettyListM x = PP.list <$> mapM prettyM x

-- Instances
------------------------------------------------------------------------

instance PP.Pretty Pattern where
  pretty e = case e of
    VarP      -> PP.text "_"
    ConP c es -> prettyApp 10 (PP.pretty c) es

prettyApp :: PP.Pretty a => Int -> PP.Doc -> [a] -> PP.Doc
prettyApp _ h []   = h
prettyApp p h args = PP.condParens (p > 3) $ h </> PP.fillSep (map (PP.prettyPrec 4) args)

-- To SI.Expr
------------------------------------------------------------------------

internalToTerm
  :: (IsTerm t, MonadTerm t m) => t -> m SI.Expr
internalToTerm t0 = do
  dontNormalize <- confDontNormalizePP <$> readConf
  tView <- view =<< if dontNormalize then return t0 else nf t0
  case tView of
    Lam body -> do
      n <- getAbsName_ body
      SI.Lam n <$> internalToTerm body
    Pi dom cod -> do
      mbCod <- strengthen_ 1 cod
      case mbCod of
        Nothing -> do
          n <- getAbsName_ cod
          SI.Pi n <$> internalToTerm dom <*> internalToTerm cod
        Just _ -> do
          -- Note that we do not use the cod on purpose: we don't want
          -- to screw up the De Bruijn numbering.
          SI.Fun <$> internalToTerm dom <*> internalToTerm cod
    Equal type_ x y ->
      SI.Equal <$> internalToTerm type_ <*> internalToTerm x <*> internalToTerm y
    Refl ->
      return $ SI.Refl SI.noSrcLoc
    Con dataCon args ->
      SI.Con dataCon <$> mapM internalToTerm args
    Set ->
      return $ SI.Set SI.noSrcLoc
    App h args -> do
      let h' = case h of
            Var v -> SI.Var (SI.name (PP.render v))
            Def f -> SI.Def f
            J -> SI.J SI.noSrcLoc
            Meta mv -> SI.Var (SI.Name (SI.srcLoc mv) (PP.render mv))
      args' <- forM args $ \arg -> case arg of
        Apply t -> SI.Apply <$> internalToTerm t
        Proj p  -> return $ SI.Proj $ pName p
      return $ SI.App h' args'
