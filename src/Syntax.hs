-- | Parsing and Scope checking, plus stuff like 'Name's and source
-- locations.
--
-- The actual data types are not exported here because they clash with
-- the 'Term' type, so you should import them like this
--
-- @
-- import qualified Syntax.Raw                       as SR
-- import qualified Syntax.Internal                  as SI
-- @
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
