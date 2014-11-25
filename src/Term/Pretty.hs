{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Term.Pretty () where

import           Prelude.Extended
import           PrettyPrint                      ((<+>), ($$), (</>), (//>), ($$>))
import qualified PrettyPrint                      as PP
import           Term.Types
import qualified Term.Subst                       as Sub

instance PrettyM t (Definition t) where
  prettyM (Constant type_ Postulate) = do
    typeDoc <- prettyM type_
    return $ "postulate" //> typeDoc
  prettyM (Constant type_ (Instantiable instk)) = do
    typeDoc <- prettyM type_
    instDoc <- prettyM instk
    return $ typeDoc $$ instDoc
  prettyM (Constant type_ (Data dataCons)) = do
    typeDoc <- prettyM type_
    return $ "data" <+> typeDoc <+> "where" $$>
             PP.vcat (map PP.pretty dataCons)
  prettyM (Constant type_ (Record dataCon fields)) = do
    typeDoc <- prettyM type_
    return $ "record" <+> typeDoc <+> "where" $$>
             "constructor" <+> PP.pretty dataCon $$
             "field" $$>
             PP.vcat (map (PP.pretty . pName) fields)
  prettyM (DataCon tyCon _ (Contextual pars type_)) = do
    typeDoc <- prettyM =<< telPi pars type_
    return $ "constructor" <+> PP.pretty tyCon $$> typeDoc
  prettyM (Projection _ tyCon (Contextual pars (type1, type2))) = do
    typeDoc <- prettyM =<< telPi pars =<< pi type1 type2
    return $ "projection" <+> PP.pretty tyCon $$> typeDoc

instance PrettyM t (Clause t) where
  prettyM (Clause pats body) = do
    bodyDoc <- prettyM body
    return $ PP.group $
      PP.hsep (map PP.pretty pats ++ ["="]) //> bodyDoc

instance PP.Pretty Pattern where
  pretty e = case e of
    VarP      -> PP.text "_"
    ConP c es -> prettyApp 10 (PP.pretty c) es

prettyApp :: PP.Pretty a => Int -> PP.Doc -> [a] -> PP.Doc
prettyApp _ h []   = h
prettyApp p h args = PP.condParens (p > 3) $ h </> PP.fillSep (map (PP.prettyPrec 4) args)

instance PrettyM t (Tel t) where
  prettyM tel00 = fmap PP.group $ case tel00 of
    T0 -> do
      return "[]"
    (n0, type0) :> tel0 -> do
      type0Doc <- prettyM type0
      tel0Doc <- go tel0
      return $ "[" <+> PP.pretty n0 <+> ":" <+> type0Doc <> whichLine tel0 <> tel0Doc
    where
      go T0 = do
        return "]"
      go ((n, type_) :> tel) = do
        typeDoc <- prettyM type_
        telDoc <- go tel
        return $ ";" <+> PP.pretty n <+> ":" <+> typeDoc <> whichLine tel <> telDoc

      whichLine T0 = PP.line
      whichLine _  = PP.linebreak

instance PrettyM t (Ctx t) where
  prettyM = prettyM . ctxToTel

instance PrettyM t (Sub.Subst t) where
  prettyM sub0 = case sub0 of
    Sub.Id -> do
      return "Id"
    Sub.Weaken i sub -> do
      subDoc <- prettyM sub
      return $ "Weaken" <+> PP.pretty i //> subDoc
    Sub.Instantiate t sub -> do
      subDoc <- prettyM sub
      tDoc <- prettyM t
      return $
        "Instantiate" $$
        "sub:" //> subDoc $$
        "term:" //> tDoc
    Sub.Strengthen i sub -> do
      subDoc <- prettyM sub
      return $ "Strengthen" <+> PP.pretty i //> subDoc
    Sub.Lift i sub -> do
      subDoc <- prettyM sub
      return $ "Lift" <+> PP.pretty i //> subDoc

instance (IsTerm t) => PrettyM t (Inst t) where
  prettyM Open = do
    return "Open"
  prettyM (Inst t) = do
    tDoc <- prettyM t
    return $ "Inst" //> tDoc

instance (IsTerm t) => PrettyM t (Invertible t) where
  prettyM = prettyM . ignoreInvertible
