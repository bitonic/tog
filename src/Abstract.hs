{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -w -fwarn-incomplete-patterns -Werror #-}
{-| Abstract syntax produced by scope checker, input for the type checker.
 -}
module Abstract where

import           TogPrelude
import           PrettyPrint
import           Names

-- * Abstract syntax.
------------------------------------------------------------------------

data Module = Module QName Params [QName] [Decl]

type Params = [(Name, Expr)]

data Decl
  = TypeSig TypeSig
  | Postulate TypeSig
  | Data TypeSig
  | Record TypeSig
  | FunDef QName [Clause]
  | DataDef QName [Name] [TypeSig]
  | RecDef  QName [Name] QName [TypeSig]
  | Module_ Module
  | Import QName [Expr]
  | Open QName

data TypeSig = Sig
  { typeSigName :: QName
  , typeSigType :: Expr
  }

data Clause = Clause [Pattern] Expr [Decl]

data Expr
  = Lam Name Expr
  | Pi Name Expr Expr
  | Fun Expr Expr
  | Equal Expr Expr Expr
  | App Head [Elim]
  | Set SrcLoc
  | Meta SrcLoc
  | Refl SrcLoc
  | Con QName [Expr]

data Head
  = Var Name
  | Def QName
  | J SrcLoc

data Elim
  = Apply Expr
  | Proj QName
  deriving Eq

data Pattern
  = VarP Name
  | WildP SrcLoc
  | ConP QName [Pattern]

-- | Number of variables bound by a list of pattern.
patternsBindings :: [Pattern] -> Int
patternsBindings = sum . map patternBindings

-- | Number of variables bound by a pattern.
patternBindings :: Pattern -> Int
patternBindings (VarP _)      = 1
patternBindings (WildP _)     = 1
patternBindings (ConP _ pats) = patternsBindings pats

-- * Instances
------------------------------------------------------------------------

instance HasSrcLoc SrcLoc where
  srcLoc = id

instance HasSrcLoc Name where
  srcLoc (Name p _) = p

instance HasSrcLoc Module where
  srcLoc (Module x _ _ _) = srcLoc x

instance HasSrcLoc Decl where
  srcLoc d = case d of
    TypeSig sig    -> srcLoc sig
    Postulate sig  -> srcLoc sig
    Data sig       -> srcLoc sig
    Record sig     -> srcLoc sig
    FunDef x _     -> srcLoc x
    DataDef x _ _  -> srcLoc x
    RecDef x _ _ _ -> srcLoc x
    Module_ x      -> srcLoc x
    Open x         -> srcLoc x
    Import x _     -> srcLoc x

instance HasSrcLoc TypeSig where
  srcLoc (Sig x _) = srcLoc x

instance HasSrcLoc Expr where
  srcLoc e = case e of
    Lam x _     -> srcLoc x
    Pi x _ _    -> srcLoc x
    Fun a _     -> srcLoc a
    Equal _ a _ -> srcLoc a
    App h _     -> srcLoc h
    Set p       -> p
    Meta p      -> p
    Con c _     -> srcLoc c
    Refl p      -> p

instance HasSrcLoc Head where
  srcLoc h = case h of
    Var x       -> srcLoc x
    Def x       -> srcLoc x
    J loc       -> loc

instance HasSrcLoc QName where
  srcLoc (QName n _) = srcLoc n

instance HasSrcLoc Pattern where
  srcLoc p = case p of
    WildP p  -> p
    VarP x   -> srcLoc x
    ConP c _ -> srcLoc c

instance HasSrcLoc Elim where
  srcLoc e = case e of
    Apply e -> srcLoc e
    Proj x  -> srcLoc x

-- | Syntactic equality (ignoring source locations).

instance Eq Expr where
  Lam x e     == Lam x' e'      = x == x' && e == e'
  Pi x a b    == Pi x' a' b'    = x == x' && a == a' && b == b'
  Fun a b     == Fun a' b'      = a == a' && b == b'
  Equal a x y == Equal a' x' y' = a == a' && x == x' && y == y'
  App h es    == App h' es'     = h == h' && es == es'
  Set _       == Set _          = True
  Meta _      == Meta _         = True
  _           == _              = False

instance Eq Head where
  Var x  == Var x' = x == x'
  Def f  == Def f' = f == f'
  J _    == J _    = True
  _      == _      = False

-- Pretty printing
------------------------------------------------------------------------

instance Show Decl    where showsPrec = defaultShow
instance Show TypeSig where showsPrec = defaultShow
instance Show Elim    where showsPrec = defaultShow
instance Show Expr    where showsPrec = defaultShow
instance Show Head    where showsPrec = defaultShow
instance Show Pattern where showsPrec = defaultShow

instance Pretty Module where
  pretty (Module name pars exports decls) =
    let parsDoc =
          let ds = [parens (pretty n <+> ":" <+> pretty ty) | (n, ty) <- pars]
          in if null ds then [] else [mconcat ds]
    in hsep ([text "module", pretty name] ++ parsDoc ++ ["where"]) $$>
       vcat (map pretty decls)

instance Pretty TypeSig where
  pretty (Sig x e) =
    pretty x <+> text ":" //> pretty e

instance Pretty Decl where
  pretty d = case d of
    TypeSig sig ->
      pretty sig
    Postulate sig ->
      text "postulate" $$> pretty sig
    Data sig ->
      text "data" $$> pretty sig
    Record sig ->
      text "record" $$> pretty sig
    FunDef f clauses ->
      vcat $ map (prettyClause f) clauses
    DataDef d xs cs ->
      hsep (text "data" : pretty d : map pretty xs ++ [text "where"]) $$>
      vcat (map pretty cs)
    RecDef r xs con fs ->
      hsep (text "record" : pretty r : map pretty xs ++ [text "where"]) $$>
      text "constructor" <+> pretty con $$
      text "field" $$>
      vcat (map pretty fs)
    Module_ m ->
      pretty m
    Open m ->
      hsep [text "open", pretty m]
    Import m args ->
      hsep (text "import" : pretty m : map (prettyPrec 4) args)
    where
      prettyClause f (Clause ps e []) =
        group (hsep (pretty f : map pretty ps ++ ["="]) //> pretty e)
      prettyClause f (Clause ps e wheres) =
        group (hsep (pretty f : map pretty ps ++ ["="]) //> pretty e) $$
        indent 2 ("where" $$ indent 2 (vcat (map pretty wheres)))

instance Pretty Head where
  pretty h = case h of
    Var x       -> pretty x
    Def f       -> pretty f
    J _         -> text "J"

instance Pretty Pattern where
  pretty e = case e of
    WildP _   -> text "_"
    VarP x    -> pretty x
    ConP c es -> parens $ sep $ pretty c : map pretty es

-- Pretty printing terms
------------------------------------------------------------------------

instance Pretty Elim where
  prettyPrec p (Apply e) = condParens (p > 0) $ "$" <+> prettyPrec p e
  prettyPrec _ (Proj x)  = "." <> pretty x

instance Pretty Expr where
  prettyPrec p e = case e of
    Set _       -> text "Set"
    Meta _      -> text "_"
    Equal (Meta _) x y ->
      condParens (p > 2) $
        prettyPrec 3 x <+> text "==" //> prettyPrec 2 y
    Equal a x y -> prettyApp p (text "_==_") [a, x, y]
    Fun a b ->
      condParens (p > 0) $ align $
        prettyPrec 1 a <+> text "->" // pretty b
    Pi{} ->
      condParens (p > 0) $ align $
        prettyTel tel <+> text "->" // pretty b
      where
        (tel, b) = piView e
        piView (Pi x a b) = ((x, a) :) *** id $ piView b
        piView a          = ([], a)
    Lam{} ->
      condParens (p > 0) $
      text "\\" <> hsep (map pretty xs) <+> text "->" <+> pretty b
      where
        (xs, b) = lamView e
        lamView (Lam x b) = (x :) *** id $ lamView b
        lamView e         = ([], e)
    App{} -> prettyApp p (pretty h) es
      where
        (h, es) = appView e
        appView (App h es) = buildApp h [] es
        appView e = error $ "impossible: pretty application"

        buildApp :: Head -> [Expr] -> [Elim] -> (Head, [Expr])
        buildApp h es0 (Apply e : es1) = buildApp h (es0 ++ [e]) es1
        buildApp h es0 (Proj f  : es1) = buildApp (Def f) [App h $ map Apply es0] es1
        buildApp h es []               = (h, es)
    Refl{} -> text "refl"
    Con c args -> prettyApp p (pretty c) args

prettyTel :: [(Name, Expr)] -> Doc
prettyTel = group . prs . reverse
  where
    prs []       = empty
    prs [b]      = pr b
    prs (b : bs) = group (prs bs) $$ pr b

    pr (x, e) = parens (pretty x <+> text ":" <+> pretty e)

