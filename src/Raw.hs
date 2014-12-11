{-# OPTIONS -fno-warn-orphans #-}
-- | Module defining the Raw syntax -- what we parse.
module Raw
  ( module Raw.Abs
  , module Raw.Print
  ) where

import Raw.Abs
import Raw.Print
import PrettyPrint

-- Pretty instances
------------------------------------------------------------------------

instance Pretty QName where
  pretty = string . printTree

instance Pretty Decl where
  pretty = string . printTree
