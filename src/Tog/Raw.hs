{-# OPTIONS -fno-warn-orphans #-}
-- | Module defining the Raw syntax -- what we parse.
module Tog.Raw
  ( module Tog.Raw.Abs
  , module Tog.Raw.Print
  ) where

import Tog.Raw.Abs
import Tog.Raw.Print
import Tog.PrettyPrint

-- Pretty instances
------------------------------------------------------------------------

instance Pretty QName where
  pretty = string . printTree

instance Pretty Decl where
  pretty = string . printTree
