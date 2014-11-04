{-# LANGUAGE OverloadedStrings #-}
import           Prelude                          hiding (interact)

import           Control.Monad.Trans.Except       (ExceptT(ExceptT), runExceptT)
import           Options.Applicative
import           Options.Applicative.Types
import           System.Exit                      (exitFailure)
import qualified System.Console.Haskeline         as Haskeline
import           Data.List.Split                  (splitOn)

import           Conf
import           PrettyPrint                      ((<+>), ($$))
import qualified PrettyPrint                      as PP
import           Prelude.Extended
import           Term
import           TypeCheck3
import           Syntax.Internal                  (scopeCheckProgram)
import           Syntax.Raw                       (parseProgram)

-- Modules that we don't need, but should compile
import           Term.Testing                     ()

parseTypeCheckConf :: Parser Conf
parseTypeCheckConf = Conf
  <$> strOption
      ( long "termType" <> short 't' <> value "GR" <>
        help "Available types: S (Simple), GR (GraphReduce), GRS (GraphReduceSub), GRU (GraphReduceUnpack), H (Hashed)."
      )
  <*> strOption
      ( long "solver" <> value "S" <>
        help "Available solvers: S (Simple), H (Hetero), TC (TwoContexts)."
      )
  <*> debugLabelsOption
      ( long "debug" <> short 'd' <> value [] <>
        help "Select debug labels to print."
      )
  <*> switch
      (long "stackTrace" <> short 's' <> help "Print debug output")
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

debugLabelsOption
  :: Mod OptionFields [(Bool, [String])]
  -> Parser [(Bool, [String])]
debugLabelsOption = option $ do
  s <- readerAsk
  return [ case x of
             []       -> (True,  [])
             '~' : x' -> (False, splitOn "." x')
             x'       -> (True,  splitOn "." x')
         | x <- splitOn "|" s
         ]

parseMain :: Parser (IO ())
parseMain =
  typeCheck
    <$> argument str (metavar "FILE")
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
      checkFile file $ \(ts, mbErr) -> do
        forM_ mbErr $ \err -> do
          putStrLn (PP.render err)
          unless interactive exitFailure
        when interactive $
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
  -> (forall t. (IsTerm t) => (TCState' t, Maybe PP.Doc) -> IO a)
  -> IO a
checkFile file ret = do
  mbErr <- runExceptT $ do
    s   <- lift $ readFile file
    raw <- exceptShowErr "Parse" $ parseProgram s
    exceptShowErr "Scope" $ scopeCheckProgram raw
  case mbErr of
    Left err  -> emptyTCState' $ \s -> ret (s, Just err)
    Right int -> checkProgram int $ \(ts, mbErr') ->
                 ret (ts, showError "Type" <$> mbErr')
  where
    showError errType err =
      PP.text errType <+> "error: " $$ PP.nest 2 err

    exceptShowErr errType =
      ExceptT . return . either (Left . showError errType) Right

main :: IO ()
main = do
  join $ execParser $ info (helper <*> parseMain) fullDesc
