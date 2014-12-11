{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Term.Pretty () where

import qualified Data.HashSet                     as HS

import           Prelude.Extended
import           Syntax
import           PrettyPrint                      ((<+>), ($$), (</>), (//>), ($$>))
import qualified PrettyPrint                      as PP
import           Term.Types
import qualified Term.Subst                       as Sub

instance (PrettyM t (f QName t), PrettyM t (f Projection t)) => PrettyM t (Definition f t) where
  prettyM (Constant type_ Postulate) = do
    typeDoc <- prettyM type_
    return $ "postulate" //> typeDoc
  prettyM (Constant type_ (Function instk)) = do
    typeDoc <- prettyM type_
    instDoc <- prettyM instk
    return $ typeDoc $$ instDoc
  prettyM (Constant type_ (Data dataCons)) = do
    typeDoc <- prettyM type_
    dataConsDocs <- mapM prettyM dataCons
    return $ "data" <+> typeDoc <+> "where" $$> PP.vcat dataConsDocs
  prettyM (Constant type_ (Record dataCon fields)) = do
    typeDoc <- prettyM type_
    dataConDoc <- prettyM dataCon
    fieldsDoc <- mapM prettyM fields
    return $ "record" <+> typeDoc <+> "where" $$>
             "constructor" <+> dataConDoc $$
             "field" $$> PP.vcat fieldsDoc
  prettyM (DataCon tyCon _ (Contextual pars type_)) = do
    tyConDoc <- prettyM tyCon
    typeDoc <- prettyM =<< telPi pars type_
    return $ "constructor" <+> tyConDoc $$> typeDoc
  prettyM (Projection _ tyCon (Contextual pars type_)) = do
    tyConDoc <- prettyM tyCon
    typeDoc <- prettyM =<< telPi pars type_
    return $ "projection" <+> tyConDoc $$> typeDoc
  prettyM (Module (Contextual tel names)) = do
    telDoc <- prettyM tel
    return $ "module" <+> telDoc <+> PP.tupled (map PP.pretty (HS.toList names))

instance PrettyM t (Clause t) where
  prettyM (Clause pats body) = do
    patsDoc <- mapM prettyM pats
    bodyDoc <- prettyM body
    return $ PP.group $
      PP.hsep (patsDoc ++ ["="]) //> bodyDoc

instance PrettyM t Name where
  prettyM = return . PP.pretty

instance PrettyM t QName where
  prettyM = return . PP.pretty

instance PrettyM t (Pattern t) where
  prettyM e = case e of
    VarP      -> return $ PP.text "_"
    ConP c es -> do cDoc <- prettyM c
                    esDoc <- mapM prettyM es
                    return $ prettyApp 10 cDoc esDoc

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
        "term:" //> tDoc $$
        "sub:" //> subDoc
    Sub.Strengthen i sub -> do
      subDoc <- prettyM sub
      return $ "Strengthen" <+> PP.pretty i //> subDoc
    Sub.Lift i sub -> do
      subDoc <- prettyM sub
      return $ "Lift" <+> PP.pretty i //> subDoc

instance (IsTerm t) => PrettyM t (FunInst t) where
  prettyM Open = do
    return "Open"
  prettyM (Inst t) = do
    tDoc <- prettyM t
    return $ "Inst" //> tDoc

instance PrettyM t (Invertible t) where
  prettyM = prettyM . ignoreInvertible

instance PrettyM t (MetaBody t) where
  prettyM mvb = prettyM =<< metaBodyToTerm mvb

instance PrettyM t (BlockedHead t) where
  prettyM (BlockedOnFunction n) = do
    nDoc <- prettyM n
    return $ "BlockedOnFunction" //> nDoc
  prettyM BlockedOnJ = do
    return "BlockedOnJ"

instance (PrettyM t a, PrettyM t b) => PrettyM t (a, b) where
  prettyM (x, y) = do
    xDoc <- prettyM x
    yDoc <- prettyM y
    return $ PP.tupled [xDoc, yDoc]

instance (PrettyM t a) => PrettyM t (Contextual t a) where
  prettyM (Contextual tel x) = do
    telDoc <- prettyM tel
    xDoc <- prettyM x
    return $
      "tel:" //> telDoc $$
      "inside:" //> xDoc

instance (PrettyM t a) => PrettyM t (Const a b) where
  prettyM (Const x) = prettyM x

instance PrettyM t Projection where
  prettyM = return . PP.pretty
