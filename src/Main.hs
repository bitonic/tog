{-# LANGUAGE OverloadedStrings #-}
import           Prelude                          hiding (interact)

import           Options.Applicative
import           Options.Applicative.Types
import           System.Exit                      (exitFailure)
import           Data.List.Split                  (splitOn)

import           Instrumentation
import           PrettyPrint                      ((<+>), ($$))
import qualified PrettyPrint                      as PP
import           TogPrelude
import           Term
import           CheckFile
import           Parse
import           ScopeCheck

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
    <*> parseTypeCheckConf
  where
    typeCheck file conf = do
      instrument conf $ do
        processFile file $ \_ mbErr -> do
          forM_ mbErr $ \err -> do
            silent <- confQuiet <$> readConf
            unless silent $ putStrLn (PP.render err)
            exitFailure

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
