{-# LANGUAGE OverloadedStrings #-}
module Main.Common (checkFile) where

import           Control.Monad.Trans.Class        (lift)
import           Control.Monad.Trans.Except       (ExceptT(ExceptT), runExceptT,)

import           Syntax.Internal                  (checkScope)
import           Syntax.Raw                       (parseProgram)
import           Term                             (IsTerm)
import           PrettyPrint                      ((<+>), ($$))
import qualified PrettyPrint                      as PP
import           TypeCheck3                       (checkProgram, TCState')

checkFile
  :: FilePath
  -> (forall t. (IsTerm t) => TCState' t -> IO a)
  -> IO (Either PP.Doc a)
checkFile file ret = runExceptT $ do
    s   <- lift $ readFile file
    raw <- ExceptT $ return $ showError "Parse" $ parseProgram s
    int <- ExceptT $ return $ showError "Scope" $ checkScope raw
    ExceptT $ fmap (showError "Type") $ checkProgram int ret
  where
    showError :: String -> Either PP.Doc b -> Either PP.Doc b
    showError errType =
      either (\err -> Left $ PP.text errType <+> "error: " $$ PP.nest 2 err) Right
