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

import           Term.Class
import           Term.Definition
import qualified Term.Signature                   as Sig
import           Term.Subst
import           Term.Synonyms
import qualified Term.Telescope                   as Tel
import           Term.Var
import           Text.PrettyPrint.Extended        ((<+>), (<>), ($$))
import qualified Text.PrettyPrint.Extended        as PP

prettyTerm :: (IsVar v, IsTerm t) => Sig.Signature t -> t v -> PP.Doc
prettyTerm sig = prettyPrecTerm sig 0

prettyPrecTerm :: (IsVar v, IsTerm t) => Sig.Signature t -> Int -> t v -> PP.Doc
prettyPrecTerm sig p t = case instantiateMetaVars sig t of
  Set ->
    PP.text "Set"
  Equal a x y ->
    prettyApp (prettyPrecTerm sig) p (PP.text "_==_") [a, x, y]
  Pi a b ->
    let mbN = getAbsName b
    in PP.condParens (p > 0) $
        PP.sep [ (PP.parens $ case mbN of
                    Nothing -> prettyTerm sig a
                    Just n  -> PP.pretty n <> PP.text " : " <> prettyTerm sig a) PP.<+>
                 PP.text "->"
               , PP.nest 2 $ prettyTerm sig b
               ]
  Lam b ->
    let n = getAbsName_ b
    in PP.condParens (p > 0) $
       PP.sep [ PP.text "\\" <> PP.pretty n <> PP.text " ->"
              , PP.nest 2 $ prettyTerm sig b
              ]
  App h es ->
    prettyApp (prettyPrecElim sig) p (PP.pretty h) es
  Refl ->
    PP.text "refl"
  Con dataCon args ->
    prettyApp (prettyPrecTerm sig) p (PP.pretty dataCon) args
  where

prettyApp :: (Int -> a -> PP.Doc) -> Int -> PP.Doc -> [a] -> PP.Doc
prettyApp _f _p h [] = h
prettyApp f   p h xs =
  PP.condParens (p > 3) $ h <+> PP.fsep (map (f 4) xs )


instantiateMetaVars :: (IsVar v, IsTerm t) => Sig.Signature t -> t v -> TermView t v
instantiateMetaVars sig t =
  case whnfView sig t of
    Lam abs' ->
      Lam abs'
    Pi dom cod ->
      Pi (go dom) cod
    Equal type_ x y ->
      Equal (go type_) (go x) (go y)
    Refl ->
      Refl
    Con dataCon ts ->
      Con dataCon $ map go ts
    Set ->
      Set
    App (Meta mv) els | Just t' <- Sig.getMetaVarBody sig mv ->
      instantiateMetaVars sig $ eliminate sig (substVacuous t') els
    App h els ->
      App h $ map goElim els
  where
    go = unview . instantiateMetaVars sig

    goElim (Proj n field) = Proj n field
    goElim (Apply t')     = Apply (go t')

prettyElim :: (IsVar v, IsTerm t) => Sig.Signature t -> Elim t v -> PP.Doc
prettyElim = error "TODO prettyElim"

prettyPrecElim :: (IsVar v, IsTerm t) => Sig.Signature t -> Int -> Elim t v -> PP.Doc
prettyPrecElim p sig (Apply e)  = prettyPrecTerm p sig e
prettyPrecElim _ _   (Proj n _) = PP.text $ show n

prettyElims :: (IsVar v, IsTerm t) => Sig.Signature t -> [Elim t v] -> PP.Doc
prettyElims = error "TODO prettyElim"

prettyDefinition :: (IsTerm t) => Sig.Signature t -> Closed (Definition t) -> PP.Doc
prettyDefinition sig (Constant Postulate type_) =
  prettyTerm sig type_
prettyDefinition sig (Constant (Data dataCons) type_) =
  "data" <+> prettyTerm sig type_ <+> "where" $$
  PP.nest 2 (PP.vcat (map PP.pretty dataCons))
prettyDefinition sig (Constant (Record dataCon fields) type_) =
  "record" <+> prettyTerm sig type_ <+> "where" $$
  PP.nest 2 ("constructor" <+> PP.pretty dataCon) $$
  PP.nest 2 ("field" $$ PP.nest 2 (PP.vcat (map (PP.pretty . fst) fields)))
prettyDefinition sig (DataCon tyCon type_) =
  "constructor" <+> PP.pretty tyCon $$ PP.nest 2 (prettyTele sig type_)
prettyDefinition sig (Projection _ tyCon type_) =
  "projection" <+> PP.pretty tyCon $$ PP.nest 2 (prettyTele sig type_)
prettyDefinition sig (Function type_ clauses) =
  prettyTerm sig type_ $$
  PP.vcat (map (prettyClause sig) (ignoreInvertible clauses))

prettyClause :: (IsTerm t) => Sig.Signature t -> Closed (Clause t) -> PP.Doc
prettyClause sig (Clause pats body) =
  PP.pretty pats <+> "=" $$ PP.nest 2 (prettyTerm sig (substFromScope body))

prettyTele
  :: forall v t.
     (IsVar v, IsTerm t)
  => Sig.Signature t -> Tel.IdTel t v -> PP.Doc
prettyTele sig (Tel.Empty (Tel.Id t)) =
   prettyTerm sig t
prettyTele sig (Tel.Cons (n0, type0) tel0) =
  "[" <+> PP.pretty n0 <+> ":" <+> prettyTerm sig type0 PP.<> go tel0
  where
    go :: forall v'. (IsVar v') => Tel.IdTel t v' -> PP.Doc
    go (Tel.Empty (Tel.Id t)) =
      "]" <+> prettyTerm sig t
    go (Tel.Cons (n, type_) tel) =
      ";" <+> PP.pretty n <+> ":" <+> prettyTerm sig type_ <+> prettyTele sig tel

-- Instances
------------------------------------------------------------------------

instance (IsVar v) => PP.Pretty (Head v) where
    pretty (Var v)   = PP.pretty (varIndex v) <> "#" <> PP.pretty (varName v)
    pretty (Def f)   = PP.pretty f
    pretty J         = PP.text "J"
    pretty (Meta mv) = PP.pretty mv

instance PP.Pretty Pattern where
  prettyPrec p e = case e of
    VarP      -> PP.text "_"
    ConP c es -> PP.prettyApp p (PP.pretty c) es
