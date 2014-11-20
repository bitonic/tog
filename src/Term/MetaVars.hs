{-# OPTIONS_GHC -fno-warn-orphans #-}
module Term.MetaVars where

import           Data.Maybe                       (fromJust)

import           Prelude.Extended
import           Term.Types
import qualified Term.Signature                   as Sig
import qualified Term.Telescope                   as Tel

instance IsTerm t => MetaVars t (Clause t) where
  metaVars (Clause _ t) = metaVars t

instance IsTerm t => MetaVars t (Invertible t) where
  metaVars (NotInvertible clauses) = metaVars clauses
  metaVars (Invertible injClauses) = metaVars $ map snd injClauses

instance (MetaVars t a, MetaVars t b) => MetaVars t (a, b) where
  metaVars (x, y) = (<>) <$> metaVars x <*> metaVars y

instance IsTerm t => MetaVars t (Definition t) where
  metaVars (Constant t c)              = metaVars (t, c)
  metaVars (DataCon _ _ pars type_)    = metaVars (pars, type_)
  metaVars (Projection _ _ pars type_) = metaVars (pars, type_)

instance IsTerm t => MetaVars t (Constant t) where
  metaVars Postulate          = return mempty
  metaVars (Data _)           = return mempty
  metaVars (Record _ _)       = return mempty
  metaVars (Function clauses) = metaVars clauses

instance MetaVars t a => MetaVars t (Maybe a) where
  metaVars Nothing  = return mempty
  metaVars (Just x) = metaVars x

instance MetaVars t (Sig.Signature t) where
  metaVars sig =
    metaVars $ map (fromJust . Sig.getDefinition sig) (Sig.definedNames sig)

instance MetaVars t (Tel.Tel t) where
  metaVars Tel.Empty                 = return mempty
  metaVars (Tel.Cons (_, type_) tel) = metaVars (type_, tel)
