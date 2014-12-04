{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Term.MetaVars where

import           Prelude.Extended
import           Syntax
import           Term.Types

instance IsTerm t => Metas t (Clause t) where
  metas (Clause _ t) = metas t

instance IsTerm t => Metas t (Invertible t) where
  metas (NotInvertible clauses) = metas clauses
  metas (Invertible injClauses) = metas $ map snd injClauses

instance (Metas t a, Metas t b) => Metas t (a, b) where
  metas (x, y) = (<>) <$> metas x <*> metas y

instance (Metas t (f QName t), Metas t (f Projection t)) => Metas t (Definition f t) where
  metas (Constant t c)             = metas (t, c)
  metas (DataCon dataCon _ type_)  = metas (dataCon, type_)
  metas (Projection _ tyCon type_) = metas (tyCon, type_)

instance (Metas t (f QName t), Metas t (f Projection t)) => Metas t (Constant f t) where
  metas Postulate               = return mempty
  metas (Data dataCon)          = metas dataCon
  metas (Record dataCon fields) = metas (dataCon, fields)
  metas (Function inst)         = metas inst

instance (IsTerm t) => Metas t (FunInst t) where
  metas Open     = return mempty
  metas (Inst t) = metas t

instance Metas t a => Metas t (Maybe a) where
  metas Nothing  = return mempty
  metas (Just x) = metas x

instance Metas t (Signature t) where
  metas sig =
    metas $ map (sigGetDefinition sig) (sigDefinedNames sig)

instance Metas t (Tel t) where
  metas T0                  = return mempty
  metas ((_, type_) :> tel) = metas (type_, tel)

instance (Metas t a) => Metas t (Contextual t a) where
  -- TODO can't we just ignore `x'?
  metas (Contextual x y) = metas (x, y)

instance Metas t Name where
  metas _ = return mempty

instance Metas t QName where
  metas _ = return mempty

instance Metas t Projection where
  metas _ = return mempty

instance (Metas t a) => Metas t (Const a b) where
  metas (Const x) = metas x

instance Metas t (MetaBody t) where
  metas = metas . mbBody
