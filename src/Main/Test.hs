{-# LANGUAGE OverloadedStrings #-}
module Main.Test (parseTest) where

import           Options.Applicative
import           System.Exit                      (exitFailure)

import           Conf
import           Main.Common
import qualified PrettyPrint                         as PP
import           PrettyPrint                         ((//>))

testConf :: String -> Conf
testConf tt = defaultConf{confTermType = tt, confQuiet = True}

parseTest' :: Parser (IO ())
parseTest' =
  subparser
    (command "fail" (info parseShouldFail (progDesc "Check that a file fails to compile.")) <>
     command "succeed" (info parseShouldSucceed (progDesc "Check that a file compiles.")))
  where
    parseShouldFail =
      shouldFail <$> argument Just (metavar "TERMTYPE") <*> argument Just (metavar "FILE")

    shouldFail tt file = do
      writeConf $ testConf tt
      mbErr <- checkFile file $ return . either Just (\_ -> Nothing)
      case mbErr of
        Just _ -> do
          putStrLn "OK"
        Nothing -> do
          putStrLn "Expecting failure, but the file compiled."
          exitFailure

    parseShouldSucceed =
      shouldSucceed <$> argument Just (metavar "TERMTYPE") <*> argument Just (metavar "FILE")

    shouldSucceed tt file = do
      writeConf $ testConf tt
      mbErr <- checkFile file $ return . either Just (\_ -> Nothing)
      case mbErr of
        Just err -> do
          putStrLn $ PP.render $
            "Expecting success, but we got an error:" //> err
          exitFailure
        Nothing -> do
          putStrLn "OK"

parseTest :: ParserInfo (IO ())
parseTest = info (helper <*> parseTest') fullDesc
