{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -w -fwarn-incomplete-patterns -Werror #-}

{-| Abstract syntax produced by scope checker, input for the type checker.
 -}

module Syntax.Abstract.Abs where

import Prelude.Extended
import PrettyPrint
import qualified Syntax.Raw as C
import qualified Data.Semigroup as Semigroup

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

-- | A qualified name is a non-empty list of names.  We store them
-- backwards, so that @M.N.f@ will be stored as @f :| [N, M]@.
data QName = QName {qNameName :: !Name, qNameModule :: ![Name]}
  deriving (Eq, Show, Ord, Read, Typeable, Generic)

instance Hashable QName

qNameCons :: Name -> QName -> QName
qNameCons n (QName n' ns) = QName n (n' : ns)

qNameSingleton :: Name -> QName
qNameSingleton n = QName n []

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

class HasSrcLoc a where
  srcLoc :: a -> SrcLoc

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

instance Pretty QName where
  pretty (QName n ns) =
    mconcat $ intersperse "." $ map pretty $ reverse (n : ns)

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

------------------------------------------------------------------------
--  HasSrcLoc instances

instance HasSrcLoc C.Name where
  srcLoc (C.Name ((l, c), _)) = SrcLoc l c

instance HasSrcLoc C.QName where
  srcLoc (C.Qual n _) = srcLoc n
  srcLoc (C.NotQual n) = srcLoc n

instance HasSrcLoc C.Expr where
  srcLoc e = case e of
    C.Lam (x:_) _ -> srcLoc x
    C.Lam [] _    -> error $ "nullary lambda: " ++ show e
    C.Pi tel _    -> srcLoc tel
    C.Fun a _     -> srcLoc a
    C.Eq x _      -> srcLoc x
    C.App (e:_)   -> srcLoc e
    C.App []      -> error "empty application"
    C.Id x        -> srcLoc x

instance HasSrcLoc C.Arg where
  srcLoc (C.Arg e)  = srcLoc e
  srcLoc (C.HArg e) = srcLoc e

instance HasSrcLoc C.Telescope where
  srcLoc (C.Tel (b : _)) = srcLoc b
  srcLoc tel = error $ "empty telescope: " ++ show tel

instance HasSrcLoc C.Binding where
  srcLoc (C.Bind  (x:_) _) = srcLoc x
  srcLoc (C.HBind (x:_) _) = srcLoc x
  srcLoc b = error $ "binding no names: " ++ show b

instance HasSrcLoc C.TypeSig where
  srcLoc (C.Sig x _) = srcLoc x

instance HasSrcLoc C.Decl where
  srcLoc d = case d of
    C.Postulate (d:_)  -> srcLoc d
    C.Postulate []     -> noSrcLoc
    C.TypeSig x        -> srcLoc x
    C.Data x _ _       -> srcLoc x
    C.Record x _ _     -> srcLoc x
    C.FunDef x _ _ _   -> srcLoc x
    C.Open x           -> srcLoc x
    C.Import x         -> srcLoc x
    C.Module_ x        -> srcLoc x
    C.OpenImport x     -> srcLoc x

instance HasSrcLoc C.Import where
  srcLoc x = case x of
    C.ImportNoArgs x -> srcLoc x
    C.ImportArgs x _ -> srcLoc x

instance HasSrcLoc C.Pattern where
  srcLoc p = case p of
    C.IdP x    -> srcLoc x
    C.AppP p _ -> srcLoc p
    C.HideP p  -> srcLoc p

instance HasSrcLoc C.Module where
  srcLoc (C.Module x _ _) = srcLoc x

instance HasSrcLoc C.Params where
  srcLoc (C.ParamDecl (x : _)) = srcLoc x
  srcLoc (C.ParamDef (x : _)) = srcLoc x
  srcLoc _ = noSrcLoc

instance HasSrcLoc C.HiddenName where
  srcLoc (C.NotHidden n) = srcLoc n
  srcLoc (C.Hidden n) = srcLoc n

