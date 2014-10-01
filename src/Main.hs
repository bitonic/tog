module Main where

import           Prelude                          hiding (interact)

import           Options.Applicative
import           System.Exit                      (exitFailure)
import qualified System.Console.Haskeline         as Haskeline

import           Conf
import           Main.Common
import qualified PrettyPrint                      as PP
import           Prelude.Extended
import           Term
import qualified Term.Signature                   as Sig
import           TypeCheck3                       (parseCommand, runCommand, TCState')
import           TypeCheck3.Monad                 (tsSignature)

parseTypeCheckConf :: Parser Conf
parseTypeCheckConf = Conf
  <$> strOption
      ( long "termType" <> short 't' <> value "S" <>
        help "Available types: S (Simple), GR (GraphReduce), H (Hashed), SUSP (Suspended)."
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
  subparser
    (command "check" parseTypeCheck)
  where
    parseInteractive =
      switch
      ( long "interactive" <> short 'i' <>
        help "Start interpreter once the file is loaded."
      )

    parseTypeCheck =
      info (typeCheck
              <$> argument Just (metavar "FILE")
              <*> parseInteractive
              <*> parseTypeCheckConf)
           (progDesc "Typecheck a file.")

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
        case parseCommand (Sig.toScope (tsSignature ts)) s of
          Left err -> do
            lift $ putStrLn $ PP.render err
            interact ts
          Right cmd -> do
            (doc, ts') <- lift $ runCommand ts cmd
            lift $ putStrLn $ PP.render doc
            interact ts'

main :: IO ()
main = do
  join $ execParser $ info (helper <*> parseMain) fullDesc
