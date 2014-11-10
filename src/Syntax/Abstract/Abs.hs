{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -w -fwarn-incomplete-patterns -Werror #-}

{-| Abstract syntax produced by scope checker, input for the type checker.
 -}

module Syntax.Abstract.Abs where

import Prelude.Extended
import PrettyPrint

-- * Source locations.
------------------------------------------------------------------------

-- | Source locations (single file only).
data SrcLoc = SrcLoc { pLine :: !Int, pCol :: !Int }
  deriving (Show, Read)

noSrcLoc = SrcLoc 0 0

instance Pretty SrcLoc where
  pretty (SrcLoc line col) = text $ concat [show line, ":", show col]

-- * Concrete names.
------------------------------------------------------------------------

-- | Concrete names coming from input.
data Name = Name { nameLoc :: !SrcLoc, nameString :: !String }
    deriving (Show, Read, Typeable, Generic)

name :: String -> Name
name s = Name noSrcLoc s

instance IsString Name where
  fromString = name

instance Eq Name where
  Name _ x == Name _ y = x == y

instance Ord Name where
  Name _ x `compare` Name _ y = compare x y

instance Hashable Name where
  hashWithSalt s (Name _ x) = hashWithSalt s x

-- * Abstract syntax.
------------------------------------------------------------------------

type Program = [Decl]

data Decl
  = TypeSig TypeSig
  | Postulate TypeSig
  | FunDef  Name [Clause]
  | DataDef Name [Name] [TypeSig]
  | RecDef  Name [Name] Name [TypeSig]

data TypeSig = Sig
  { typeSigName :: Name
  , typeSigType :: Expr
  }

data Clause = Clause [Pattern] Expr

data Expr
  = Lam Name Expr
  | Pi Name Expr Expr
  | Fun Expr Expr
  | Equal Expr Expr Expr
  | App Head [Elim]
  | Set SrcLoc
  | Meta SrcLoc
  | Refl SrcLoc
  | Con Name [Expr]

data Head
  = Var Name
  | Def Name
  | J SrcLoc

data Elim
  = Apply Expr
  | Proj Name
  deriving Eq

data Pattern
  = VarP Name
  | WildP SrcLoc
  | ConP Name [Pattern]

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

class HasSrcLoc a where
  srcLoc :: a -> SrcLoc

instance HasSrcLoc SrcLoc where
  srcLoc = id

instance HasSrcLoc Name where
  srcLoc (Name p _) = p

instance HasSrcLoc Decl where
  srcLoc d = case d of
    TypeSig sig    -> srcLoc sig
    Postulate sig  -> srcLoc sig
    FunDef x _     -> srcLoc x
    DataDef x _ _  -> srcLoc x
    RecDef x _ _ _ -> srcLoc x

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

instance Pretty Name where
  pretty (Name _ x) = text x

instance Pretty TypeSig where
  pretty (Sig x e) =
    pretty x <+> text ":" //> pretty e

instance Pretty Decl where
  pretty d = case d of
    TypeSig sig ->
      pretty sig
    Postulate sig ->
      text "postulate" $$> pretty sig
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
    where
      prettyClause f (Clause ps e) =
        group (hsep (pretty f : map pretty ps ++ ["="]) //> pretty e)

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
