{-# OPTIONS_GHC -w -fwarn-incomplete-patterns -Werror #-}
module Syntax.Raw
  ( -- * Syntax tree
    module Syntax.Raw.Abs
    -- * Pretty printing
  , module Syntax.Raw.Print
    -- * Parsing
  , parseModule
  , parseExpr
  ) where

import           Data.Maybe                       (isJust, fromJust, isNothing, fromJust)

import           Prelude.Extended
import           Syntax.Raw.Abs
import           Syntax.Raw.ErrM                  (Err(Bad, Ok))
import           Syntax.Raw.Layout                (resolveLayout)
import           Syntax.Raw.Par                   (myLexer, pModule, pExpr)
import           Syntax.Raw.Print
import qualified PrettyPrint                      as PP

parseModule :: String -> Either PP.Doc Module
parseModule s =
  case pModule (resolveLayout True (myLexer s)) of
    Bad err -> Left $ PP.text err
    Ok p    -> Right p

parseExpr :: String -> Either PP.Doc Expr
parseExpr s =
  case pExpr (resolveLayout False (myLexer s)) of
    Bad err -> Left $ PP.text err
    Ok p    -> Right p

-- Pretty instances
------------------------------------------------------------------------

instance PP.Pretty QName where
  pretty = PP.string . printTree

instance PP.Pretty Decl where
  pretty = PP.string . printTree
