module Tog.Parse (parseModule, parseExpr) where

import           Tog.Raw
import           Tog.Raw.ErrM                     (Err(Bad, Ok))
import           Tog.Raw.Layout                   (resolveLayout)
import           Tog.Raw.Par                      (myLexer, pModule, pExpr)
import qualified Tog.PrettyPrint                  as PP

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
