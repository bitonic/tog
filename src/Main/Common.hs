{-# LANGUAGE OverloadedStrings #-}
module Main.Common (checkFile) where

import           Control.Monad.Trans.Class        (lift)
import           Control.Monad.Trans.Either       (EitherT(EitherT), runEitherT, hoistEither)

import           Syntax.Internal                  (checkScope)
import           Syntax.Raw                       (parseProgram)
import           Term                             (IsTerm)
import           PrettyPrint                      ((<+>), ($$))
import qualified PrettyPrint                      as PP
import           TypeCheck                        (TypeCheckConf, checkProgram, TCState')

checkFile
  :: TypeCheckConf -> FilePath
  -> (forall t. (IsTerm t) => TCState' t -> IO a)
  -> IO (Either PP.Doc a)
checkFile conf file ret = runEitherT $ do
    s   <- lift $ readFile file
    raw <- hoistEither $ showError "Parse" $ parseProgram s
    int <- hoistEither $ showError "Scope" $ checkScope raw
    EitherT $ fmap (showError "Type") $ checkProgram conf int ret
  where
    showError :: String -> Either PP.Doc b -> Either PP.Doc b
    showError errType =
      either (\err -> Left $ PP.text errType <+> "error: " $$ PP.nest 2 err) Right
