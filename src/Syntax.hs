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
module Syntax
  ( -- * Parsing
    parseModule
  , parseExpr
    -- * Name
  , Syntax.Abstract.Name(..)
  , Syntax.Abstract.QName(..)
  , Syntax.Abstract.SrcLoc(..)
  , Syntax.Abstract.noSrcLoc
  , Syntax.Abstract.HasSrcLoc(..)
    -- * Scope checking
  , scopeCheckModule
  ) where

import Syntax.Abstract
import Syntax.Raw
