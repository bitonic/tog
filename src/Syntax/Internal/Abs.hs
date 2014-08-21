{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -w -fwarn-incomplete-patterns -Werror #-}
module Syntax.Internal.Abs where

import Prelude.Extended hiding ((<>))
import PrettyPrint

data SrcLoc = SrcLoc { pLine :: !Int, pCol :: !Int }

noSrcLoc = SrcLoc 0 0

instance Show SrcLoc where
  show (SrcLoc line col) = concat [show line, ":", show col]

instance Pretty SrcLoc where
  pretty = text . show

data Name = Name { nameLoc :: !SrcLoc, nameString :: !String }
    deriving (Typeable, Generic)

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

type Program = [Decl]

data Decl = TypeSig TypeSig
          | FunDef  Name [Clause]
          | DataDef Name [Name] [TypeSig]
          | RecDef  Name [Name] Name [TypeSig]

data TypeSig = Sig { typeSigName :: Name
                   , typeSigType :: Expr
                   }

data Clause = Clause [Pattern] Expr

data Expr = Lam Name Expr
          | Pi Name Expr Expr
          | Fun Expr Expr
          | Equal Expr Expr Expr
          | App Head [Elim]
          | Set SrcLoc
          | Meta SrcLoc
          | Refl SrcLoc
          | Con Name [Expr]

data Head = Var Name
          | Def Name
          | J SrcLoc
          | TermVar Int Name
          | TermMeta MetaVar

data Elim = Apply Expr
          | Proj Name
  deriving Eq

data Pattern = VarP Name
             | WildP SrcLoc
             | ConP Name [Pattern]

patternsBindings :: [Pattern] -> Int
patternsBindings = sum . map patternBindings

patternBindings :: Pattern -> Int
patternBindings (VarP _)      = 1
patternBindings (WildP _)     = 1
patternBindings (ConP _ pats) = patternsBindings pats

class HasSrcLoc a where
  srcLoc :: a -> SrcLoc

instance HasSrcLoc SrcLoc where
  srcLoc = id

instance HasSrcLoc Name where
  srcLoc (Name p _) = p

instance HasSrcLoc Decl where
  srcLoc d = case d of
    TypeSig sig    -> srcLoc sig
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
    TermVar _ x -> srcLoc x
    Def x       -> srcLoc x
    J loc       -> loc
    TermMeta mv -> srcLoc mv

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

instance Show Name    where showsPrec = defaultShow
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
    TermVar i x -> pretty i <> "#" <> pretty x
    J _         -> text "J"
    TermMeta mv -> pretty mv

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

prettyApp :: Pretty a => Int -> Doc -> [a] -> Doc
prettyApp _ h []   = h
prettyApp p h args0 = condParens (p > 3) $ h <> nest 2 (group (prettyArgs (reverse args0)))
  where
    prettyArgs []           = empty
    prettyArgs [arg]        = line <> prettyPrec 4 arg
    prettyArgs (arg : args) = group (prettyArgs args) $$ prettyPrec 4 arg

-- 'MetaVar'iables
------------------------------------------------------------------------

-- | 'MetaVar'iables.  Globally scoped.
data MetaVar = MetaVar
  { mvId     :: !Int
  , mvSrcLoc :: !SrcLoc
  } deriving (Generic)

instance Eq MetaVar where
  (==) = (==) `on` mvId

instance Ord MetaVar where
  compare = comparing mvId

instance Hashable MetaVar where
  hashWithSalt s = hashWithSalt s . mvId

instance Pretty MetaVar where
    prettyPrec _ = text . show

instance Show MetaVar where
   show (MetaVar mv _) = "_" ++ show mv

instance HasSrcLoc MetaVar where
  srcLoc = mvSrcLoc
