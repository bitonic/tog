module Syntax
  ( -- * Parsing
    parseProgram
  , parseExpr
    -- * Name
  , Syntax.Internal.Name(..)
  , Syntax.Internal.SrcLoc(..)
  , Syntax.Internal.HasSrcLoc(..)
    -- * Scope checking
  , scopeCheckProgram
  , scopeCheckExpr
  , Scope(..)
  , NameInfo(..)
  ) where

import Syntax.Internal
import Syntax.Raw
