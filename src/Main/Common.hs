{-# LANGUAGE OverloadedStrings #-}
module Main.Common (checkFile) where

import           Control.Monad.Trans.Class        (lift)
import           Control.Monad.Trans.Except       (ExceptT(ExceptT), runExceptT,)

import           Syntax.Internal                  (scopeCheckProgram)
import           Syntax.Raw                       (parseProgram)
import           Term                             (IsTerm)
import           Term.Impl                        (Simple)
import           PrettyPrint                      ((<+>), ($$))
import qualified PrettyPrint                      as PP
import           TypeCheck3                       (checkProgram, TCState')

checkFile
  :: FilePath
  -> (forall t. (IsTerm t) => Either PP.Doc (TCState' t) -> IO a)
  -> IO a
checkFile file ret = do
  mbErr <- runExceptT $ do
    s   <- lift $ readFile file
    raw <- ExceptT $ return $ showError "Parse" $ parseProgram s
    ExceptT $ return $ showError "Scope" $ scopeCheckProgram raw
  case mbErr of
    Left err  -> ret (Left err :: Either PP.Doc (TCState' Simple))
    Right int -> checkProgram int $ \ts -> ret (showError "Type" ts)
  where
    showError :: String -> Either PP.Doc b -> Either PP.Doc b
    showError errType =
      either (\err -> Left $ PP.text errType <+> "error: " $$ PP.nest 2 err) Right
