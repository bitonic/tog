{-# LANGUAGE OverloadedStrings #-}
import           Prelude                          hiding (interact)

import           Control.Monad.Trans.Except       (ExceptT(ExceptT), runExceptT)
import           Options.Applicative
import           System.Exit                      (exitFailure)
import qualified System.Console.Haskeline         as Haskeline

import           Conf
import           PrettyPrint                      ((<+>), ($$))
import qualified PrettyPrint                      as PP
import           Prelude.Extended
import           Term
import           Term.Impl                        (Simple)
import           TypeCheck3
import           Syntax.Internal                  (scopeCheckProgram)
import           Syntax.Raw                       (parseProgram)

parseTypeCheckConf :: Parser Conf
parseTypeCheckConf = Conf
  <$> strOption
      ( long "termType" <> short 't' <> value "S" <>
        help "Available types: S (Simple), GR (GraphReduce), H (Hashed)."
      )
  <*> strOption
      ( long "solver" <> value "S" <>
        help "Available solvers: S (Simple), TW (TwoContexts)."
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
  <*> switch
      (long "debug" <> short 'd' <> help "Print debug output")
  <*> switch
      ( long "checkMetaVarConsistency" <>
        help "Check consistency of instantiated term of a metavar and its type."
      )
  <*> switch
      ( long "fastGetAbsName" <>
        help "Do not spend time getting bound names in abstractions."
      )
  <*> switch
      ( long "disableSynEquality" <>
        help "Disable syntactic equality"
      )
  <*> switch
      ( long "dontNormalizePP" <>
        help "Don't normalize terms before pretty printing them"
      )

parseMain :: Parser (IO ())
parseMain =
  typeCheck
    <$> argument Just (metavar "FILE")
    <*> parseInteractive
    <*> parseTypeCheckConf
  where
    parseInteractive =
      switch
      ( long "interactive" <> short 'i' <>
        help "Start interpreter once the file is loaded."
      )

    typeCheck file interactive conf = do
      writeConf conf
      checkFile file $ \errOrTs ->
        case errOrTs of
          Left err -> putStrLn (PP.render err) >> exitFailure
          Right ts -> when interactive $
                      Haskeline.runInputT interactSettings (interact ts)

    interactSettings = Haskeline.defaultSettings
      { Haskeline.historyFile    = Just "~/.tog_history"
      , Haskeline.autoAddHistory = True
      }

    interact :: (IsTerm t) => TCState' t -> Haskeline.InputT IO ()
    interact ts = do
      mbS <- Haskeline.getInputLine "> "
      forM_ mbS $ \s ->
        case parseCommand ts s of
          Left err -> do
            lift $ putStrLn $ PP.render err
            interact ts
          Right cmd -> do
            (doc, ts') <- lift $ runCommand ts cmd
            lift $ putStrLn $ PP.render doc
            interact ts'

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

main :: IO ()
main = do
  join $ execParser $ info (helper <*> parseMain) fullDesc
