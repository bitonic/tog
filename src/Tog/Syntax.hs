-- | Parsing and Scope checking, plus stuff like 'Name's and source
-- locations.
--
-- The actual data types are not exported here because they clash with
-- the 'Term' type, so you should import them like this
--
-- @
-- import qualified Syntax.Raw                       as SR
-- import qualified Syntax.Abstract                  as SA
-- @
module Tog.Syntax
  ( -- * Parsing
    parseModule
  , parseExpr
    -- * Name
  , Tog.Syntax.Abstract.Name(..)
  , Tog.Syntax.Abstract.QName(..)
  , Tog.Syntax.Abstract.SrcLoc(..)
  , Tog.Syntax.Abstract.noSrcLoc
  , Tog.Syntax.Abstract.HasSrcLoc(..)
    -- * Scope checking
  , scopeCheckModule
  ) where

import Tog.Syntax.Abstract
import Tog.Syntax.Raw
