module Main where

import           Control.Monad                    (join)
import           Options.Applicative
import           System.Exit                      (exitFailure)

import           Main.Common
import qualified PrettyPrint                      as PP
import           TypeCheck2                       (TypeCheckConf(TypeCheckConf))

parseTypeCheckConf :: Parser TypeCheckConf
parseTypeCheckConf = TypeCheckConf
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

parseMain :: Parser (IO ())
parseMain =
  subparser
    (command "check" parseTypeCheck)
  where
    parseTypeCheck =
      info (typeCheck <$> argument Just (metavar "FILE") <*> parseTypeCheckConf)
           (progDesc "Typecheck a file.")

    typeCheck file conf = do
      errOrTs <- checkFile conf file $ \_ -> return ()
      case errOrTs of
        Left err -> putStrLn (PP.render err) >> exitFailure
        _        -> return ()

main :: IO ()
main = do
  join $ execParser $ info (helper <*> parseMain) fullDesc
