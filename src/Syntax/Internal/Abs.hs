{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -w -fwarn-incomplete-patterns -Werror #-}
module Syntax.Internal.Abs where

import Data.String (IsString(fromString))
import Data.Typeable (Typeable)
import Control.Arrow                    ((***))
import Data.Hashable (Hashable, hashWithSalt)
import Text.PrettyPrint.Extended

data SrcLoc = SrcLoc { pLine :: Int, pCol :: Int }

noSrcLoc = SrcLoc 0 0

instance Show SrcLoc where
  show (SrcLoc line col) = concat [show line, ":", show col]

data Name = Name { nameLoc :: SrcLoc, nameString :: String }
    deriving (Typeable)

data DefName
    = SimpleName Name
    | SyntheticName Name Int
    deriving (Eq, Ord)

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

instance HasSrcLoc DefName where
  srcLoc dn = case dn of
    SimpleName n      -> srcLoc n
    SyntheticName n _ -> srcLoc n

instance Show DefName where
  show = render . pretty

instance Hashable DefName where
  hashWithSalt s dn = hashWithSalt s $ case dn of
    SimpleName n      -> Left n
    SyntheticName n i -> Right (n, i)

type Program = [Decl]

data Decl = TypeSig TypeSig
          | FunDef  Name [Clause]
          | DataDef Name [Name] [TypeSig]
          | RecDef  Name [Name] Name [TypeSig]

data TypeSig = Sig { typeSigName :: Name
                   , typeSigType :: Expr
                   }

data Clause = Clause [Pattern] Expr [Decl]

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
          | Def DefName
          | J SrcLoc
          | TermVar Int Name
          | TermMeta Int

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
    TermMeta _  -> noSrcLoc

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
instance Show Expr    where showsPrec = defaultShow
instance Show Head    where showsPrec = defaultShow
instance Show Pattern where showsPrec = defaultShow

instance Show Elim where
  showsPrec p (Apply e) = showParen (p > 0) $ showString "$ " . shows e
  showsPrec _ (Proj x) = showString "." . shows x

instance Pretty Elim where
  pretty = text . show

instance Pretty Name where
  pretty (Name _ x) = text x

instance Pretty TypeSig where
  pretty (Sig x e) =
    sep [ pretty x <+> text ":"
        , nest 2 $ pretty e ]

instance Pretty Decl where
  pretty d = case d of
    TypeSig sig -> pretty sig
    FunDef f clauses -> vcat $
      [ vcat $ [ sep [ pretty f <+> fsep (map (prettyPrec 10) ps)
                     , nest 2 $ text "=" <+> pretty e ]
               ] ++
               (if null wheres then [] else nest 2 (text "where") : map (nest 2 . pretty) wheres)
      | Clause ps e wheres <- clauses
      ]
    DataDef d xs cs ->
      vcat [ text "data" <+> pretty d <+> fsep (map pretty xs) <+> text "where"
           , nest 2 $ vcat $ map pretty cs ]
    RecDef r xs con fs ->
      vcat [ text "record" <+> pretty r <+> fsep (map pretty xs) <+> text "where"
           , nest 2 $ vcat [ text "constructor" <+> pretty con
                           , sep [ text "field"
                                 , nest 2 $ vcat $ map pretty fs ] ] ]

instance Pretty Expr where
  prettyPrec p e = case e of
    Set _       -> text "Set"
    Meta _      -> text "_"
    Equal (Meta _) x y ->
      condParens (p > 2) $
        sep [ prettyPrec 3 x <+> text "=="
            , nest 2 $ prettyPrec 2 y ]
    Equal a x y -> prettyApp p (text "_==_") [a, x, y]
    Fun a b ->
      condParens (p > 0) $
        sep [ prettyPrec 1 a <+> text "->"
            , pretty b ]
    Pi{} ->
      condParens (p > 0) $
        sep [ prettyTel tel <+> text "->"
            , nest 2 $ pretty b ]
      where
        (tel, b) = piView e
        piView (Pi x a b) = ((x, a) :) *** id $ piView b
        piView a          = ([], a)
    Lam{} ->
      condParens (p > 0) $
      sep [ text "\\" <+> fsep (map pretty xs) <+> text "->"
          , nest 2 $ pretty b ]
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
        buildApp h es0 (Proj f  : es1) = buildApp (Def (SimpleName f)) [App h $ map Apply es0] es1
        buildApp h es []               = (h, es)
    Refl{} -> text "refl"
    Con c args -> prettyApp p (pretty c) args

instance Pretty Head where
  pretty h = case h of
    Var x       -> pretty x
    Def f       -> pretty f
    TermVar i x -> pretty i <> "#" <> pretty x
    J _         -> text "J"
    TermMeta mv -> "_" <> pretty mv

instance Pretty DefName where
  pretty dn = case dn of
    SimpleName n      -> pretty n
    SyntheticName n i -> pretty n <> "_" <> pretty i

instance Pretty Pattern where
  prettyPrec p e = case e of
    WildP _ -> text "_"
    VarP x  -> pretty x
    ConP c es -> prettyApp p (pretty c) es

prettyTel :: [(Name, Expr)] -> Doc
prettyTel bs = fsep (map pr bs)
  where
    pr (x, e) = parens (pretty x <+> text ":" <+> pretty e)
