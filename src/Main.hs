{-# LANGUAGE OverloadedStrings #-}
import           Prelude                          hiding (interact)

import           Options.Applicative
import           Options.Applicative.Types
import           System.Exit                      (exitFailure)
import qualified System.Console.Haskeline         as Haskeline
import           Data.List.Split                  (splitOn)

import           Instrumentation
import           PrettyPrint                      ((<+>), ($$))
import qualified PrettyPrint                      as PP
import           Prelude.Extended
import           Term
import           TypeCheck3
import           Syntax

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
      ( long "debug" <> short 'd' <> value mempty <>
        help "Select debug labels to print."
      )
  <*> switch
      ( long "stackTrace" <> short 's' <>
        help "Print a stack trace on error."
      )
  <*> switch
      (long "quiet" <> short 'q' <> help "Do not print any output.")
  <*> switch
      ( long "noMetasSummary" <>
        help "Do not print a summary of the metavariables state."
      )
  <*> switch
      ( long "metasReport" <>
        help "Print a detailed report of the metavariables state."
      )
  <*> switch
      ( long "metasOnlyUnsolved" <>
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
      ( long "checkMetaConsistency" <>
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
  <*> switch
      ( long "whnfApplySubst" <>
        help "Reduce term when applying a substitution"
      )
  <*> switch
      ( long "timeSections" <>
        help "Measure how much time is taken by each debug section"
      )
  <*> switch
      ( long "whnfEliminate" <>
        help "Reduce term when eliminating a term"
      )

debugLabelsOption
  :: Mod OptionFields DebugLabels
  -> Parser DebugLabels
debugLabelsOption = option $ do
  s <- readerAsk
  case s of
    [] -> return DLAll
    _  -> return $ DLSome $ splitOn "|" s

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

    typeCheck file interactive conf0 = do
      conf <- if interactive && confDebug conf0
        then do
          putStrLn "-i incompatible with -d, disabling -d"
          return $ confDisableDebug conf0
        else return conf0
      instrument conf $ do
        processFile file $ \ts mbErr -> do
          forM_ mbErr $ \err -> do
            putStrLn (PP.render err)
            unless interactive exitFailure
          when interactive $
            Haskeline.runInputT interactSettings (interact' ts)

    interactSettings = Haskeline.defaultSettings
      { Haskeline.historyFile    = Just "~/.tog_history"
      , Haskeline.autoAddHistory = True
      }

    interact' = error "TODO"
{-
    interact' :: (IsTerm t) => TCState' t -> Haskeline.InputT IO ()
    interact' ts = do
      mbS <- Haskeline.getInputLine "> "
      forM_ mbS $ \s ->
        case parseCommand ts s of
          Left err -> do
            lift $ putStrLn $ PP.render err
            interact' ts
          Right cmd -> do
            (doc, ts') <- lift $ runCommand ts cmd
            lift $ putStrLn $ PP.render doc
            interact' ts'
-}

processFile
  :: FilePath
  -> (forall t. (IsTerm t) => Signature t -> Maybe PP.Doc -> IO a)
  -> IO a
processFile file ret = do
  mbErr <- runExceptT $ do
    s   <- lift $ readFile file
    raw <- exceptShowErr "Parse" $ parseModule s
    exceptShowErr "Scope" $ scopeCheckModule raw
  case mbErr of
    Left err  -> ret (sigEmpty :: Signature Simple) (Just err)
    Right int -> checkFile int $ \sig mbErr' ->
                 ret sig (showError "Type" <$> mbErr')
  where
    showError errType err =
      PP.text errType <+> "error: " $$ PP.nest 2 err

    exceptShowErr errType =
      ExceptT . return . either (Left . showError errType) Right

main :: IO ()
main = do
  join $ execParser $ info (helper <*> parseMain) fullDesc
