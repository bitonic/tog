{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
-- | Qualified and unqualified names with source locations.
module Names
  ( -- * SrcLoc
    SrcLoc(..)
  , noSrcLoc
  , HasSrcLoc(..)
    -- * Names
  , Name(..)
  , mkName
  , QName(..)
  , qNameCons
  , qNameSingleton
  ) where

import           TogPrelude
import           PrettyPrint                      (Pretty, pretty, text)
import qualified Raw                              as C

-- * Source locations.
------------------------------------------------------------------------

-- | Source locations (single file only).
data SrcLoc = SrcLoc { pLine :: !Int, pCol :: !Int }
  deriving (Show, Read)

noSrcLoc :: SrcLoc
noSrcLoc = SrcLoc 0 0

instance Pretty SrcLoc where
  pretty (SrcLoc line col) = text $ concat [show line, ":", show col]

class HasSrcLoc a where
  srcLoc :: a -> SrcLoc

-- * Concrete names.
------------------------------------------------------------------------

-- | Concrete names coming from input.
data Name = Name { nameLoc :: !SrcLoc, nameString :: !String }
    deriving (Show, Read, Typeable, Generic)

mkName :: String -> Name
mkName s = Name noSrcLoc s

instance IsString Name where
  fromString = mkName

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

-- Pretty printing
------------------------------------------------------------------------

instance Pretty Name where
  pretty (Name _ x) = text x

instance Pretty QName where
  pretty (QName n ns) =
    mconcat $ intersperse "." $ map pretty $ reverse (n : ns)


