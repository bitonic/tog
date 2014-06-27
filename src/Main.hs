module Main where

import           Control.Monad.Trans.Class        (lift)
import           Control.Monad.Trans.Either       (EitherT(EitherT), runEitherT, hoistEither)
import           Options.Applicative
import           System.Exit                      (exitFailure)

import           Syntax.Raw                       (parseProgram)
import           Syntax.Internal                  (checkScope)
import           Term                             (IsTerm)
import           TypeCheck                        (TypeCheckConf(TypeCheckConf), checkProgram, TCState')

parseTypeCheckConf :: Parser TypeCheckConf
parseTypeCheckConf = TypeCheckConf
  <$> strOption (long "termType" <> value "GR")
  <*> flag True False (long "metaVarsSummary")
  <*> switch (long "metaVarsReport")
  <*> switch (long "metaVarsOnlyUnsolved")
  <*> flag True False (long "problemsSummary")
  <*> switch (long "problemsReport")

checkFile
  :: TypeCheckConf -> FilePath
  -> (forall t. (IsTerm t) => TCState' t -> IO a)
  -> IO (Either String a)
checkFile conf file ret = runEitherT $ do
    s   <- lift $ readFile file
    raw <- hoistEither $ showError "Parse" $ parseProgram s
    int <- hoistEither $ showError "Scope" $ checkScope raw
    EitherT $ fmap (showError "Type") $ checkProgram conf int ret
  where
    showError :: Show a => String -> Either a b -> Either String b
    showError errType = either (\err -> Left $ errType ++ " error: " ++ show err) Right

main :: IO ()
main = do
  let p = (,) <$> argument Just (metavar "FILE") <*> parseTypeCheckConf
  (file, conf) <- execParser $ info (helper <*> p) fullDesc
  errOrTs <- checkFile conf file $ \_ -> return ()
  case errOrTs of
    Left err -> putStrLn err >> exitFailure
    _        -> return ()

