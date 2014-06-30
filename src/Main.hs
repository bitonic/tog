module Main where

import           Control.Monad                    (join)
import           Control.Monad.Trans.Class        (lift)
import           Control.Monad.Trans.Either       (EitherT(EitherT), runEitherT, hoistEither)
import           Options.Applicative
import           System.Exit                      (exitFailure)

import           Syntax.Internal                  (checkScope)
import           Syntax.Raw                       (parseProgram)
import           Term                             (IsTerm)
import           Test                             (parseTest)
import           TypeCheck                        (TypeCheckConf(TypeCheckConf), checkProgram, TCState')

parseTypeCheckConf :: Parser TypeCheckConf
parseTypeCheckConf = TypeCheckConf
  <$> strOption
      ( long "termType" <> short 't' <> value "GR" <>
        help "Available types: S (Simple), GR (GraphReduce)."
      )
  <*> switch
      (long "quiet" <> short 'q' <> help "Do not print any output.")
  <*> switch
      ( long "noMetaVarsSummary" <>
        help "Do not print a summary of the metavariables state."
      )
  <*> switch
      ( long "metaVarsReport" <>
        help "Print a detailed report of the metavariables state."
      )
  <*> switch
      ( long "metaVarsOnlyUnsolved" <>
        help "In the metavariable report, only print information about the unsolved metavariables."
      )
  <*> switch
      ( long "noProblemsSummary" <>
        help "Do not print a summary of the unsolved problems."
      )
  <*> switch
      ( long "problemsReport" <>
        help "Print a detailed report of the unsolved problems."
      )

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

parseMain :: Parser (IO ())
parseMain =
  subparser
    (command "check" parseTypeCheck <> command "test" parseTest)
  where
    parseTypeCheck =
      info (typeCheck <$> argument Just (metavar "FILE") <*> parseTypeCheckConf)
           (progDesc "Typecheck a file.")

    typeCheck file conf = do
      errOrTs <- checkFile conf file $ \_ -> return ()
      case errOrTs of
        Left err -> putStrLn err >> exitFailure
        _        -> return ()

-- main :: IO ()
-- main = do
--   let p = (,) <$> argument Just (metavar "FILE") <*> parseTypeCheckConf
--   (file, conf) <- execParser $ info (helper <*> p) fullDesc
--   errOrTs <- checkFile conf file $ \_ -> return ()
--   case errOrTs of
--     Left err -> putStrLn err >> exitFailure
--     _        -> return ()

main :: IO ()
main = do
  join $ execParser $ info (helper <*> parseMain) fullDesc