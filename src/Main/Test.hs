{-# LANGUAGE OverloadedStrings #-}
module Main.Test (parseTest) where

import           Control.Monad                    (forM_, unless)
import           Control.Monad.Trans.Class        (lift)
import           Control.Monad.Trans.Either       (runEitherT, left)
import qualified Data.HashMap.Strict              as HMS
import           Data.List                        (sort)
import           Options.Applicative
import           System.Exit                      (exitFailure)

import           Main.Common
import           Syntax.Internal                  (checkScope)
import qualified Syntax.Internal                  as A
import           Syntax.Raw                       (parseProgram)
import           Term
import qualified Term.Signature                   as Sig
import           Text.PrettyPrint.Extended        (($$))
import qualified Text.PrettyPrint.Extended        as PP
import           TypeCheck
import           TypeCheck.Monad

newtype CaptureReport = CR (forall a. (forall t. (IsTerm t) => TCReport' t -> a) -> a)

testTypeCheckConf :: String -> TypeCheckConf
testTypeCheckConf tt = defaultTypeCheckConf{tccTermType = tt}

implConsistency
  :: String -> String -> [A.Decl]
  -> IO (Either PP.Doc PP.Doc)
implConsistency termType1 termType2 prog = do
  errOrReport1 <- checkProgram (testTypeCheckConf termType1) prog captureReport
  errOrReport2 <- checkProgram (testTypeCheckConf termType2) prog captureReport
  case (errOrReport1, errOrReport2) of
    (Left err1, Left err2) ->
      return $ Right $ "Both failed, with errors" $$ PP.nest 2 err1 $$
                      "and error" $$ PP.nest 2 err2
    (Right (CR cr1), Right (CR cr2)) ->
      cr1 $ \report1 -> cr2 $ \report2 -> do
        let numUnsolvedProblems1 = HMS.size $ trUnsolvedProblems report1
        let numUnsolvedProblems2 = HMS.size $ trUnsolvedProblems report2
        if (numUnsolvedProblems1 == 0 && numUnsolvedProblems2 == 0)
          then compareSignatures (trSignature report1) (trSignature report2)
          else return $ Right $ "Both have unsolved problems"
    (_, _) -> do
      return $ Left "One succeded, the other didn't."
  where
    captureReport :: (IsTerm t) => TCState' t -> IO CaptureReport
    captureReport ts = return $ CR $ \f -> f $ tcReport ts

compareSignatures
  :: (IsTerm t1, IsTerm t2)
  => Sig.Signature t1 -> Sig.Signature t2
  -> IO (Either PP.Doc PP.Doc)
compareSignatures sig1 sig2 = do
  if (sort (Sig.definedNames sig1) == sort (Sig.definedNames sig2))
    then runEitherT $ do
      let names = Sig.definedNames sig1
      forM_ names $ \name -> do
        def1 <- lift $ nf' sig1 $ Sig.getDefinition sig1 name
        def2 <- lift $ nf' sig2 $ Sig.getDefinition sig2 name
        defEqual <- lift $ definitionEq' def1 def2
        unless (defEqual) $ do
          def1Doc <- lift $ prettyDefinition sig1 def1
          def2Doc <- lift $ prettyDefinition sig2 def2
          left $ "Differing definitions" $$ PP.nest 2 def1Doc $$
                 "and" $$ PP.nest 2 def2Doc
      return "OK"
    else do
      return $ Left "Different defined names"

parseTest' :: Parser (IO ())
parseTest' =
  subparser
    (command "consistency" (info parseConsistency (progDesc "Check consistency of two term types.")) <>
     command "fail" (info parseShouldFail (progDesc "Check that a file fails to compile.")) <>
     command "succeed" (info parseShouldSucceed (progDesc "Check that a file compiles.")))
  where
    parseConsistency =
      consistency <$> argument Just (metavar "TERMTYPE")
                  <*> argument Just (metavar "TERMTYPE")
                  <*> argument Just (metavar "FILE")

    consistency tt1 tt2 file = do
      s <- readFile file
      let Right raw = parseProgram s
      let Right int = checkScope raw
      mbErr <- implConsistency tt1 tt2 int
      case mbErr of
        Left err -> do
          putStrLn $ PP.render err
          exitFailure
        Right ok ->
          putStrLn $ PP.render ok

    parseShouldFail =
      shouldFail <$> argument Just (metavar "TERMTYPE") <*> argument Just (metavar "FILE")

    shouldFail tt file = do
      mbErr <- checkFile (testTypeCheckConf tt) file $ \_ -> return ()
      case mbErr of
        Left _ -> do
          putStrLn "OK"
        Right _ -> do
          putStrLn "Expecting failure, but the file compiled."
          exitFailure

    parseShouldSucceed =
      shouldSucceed <$> argument Just (metavar "TERMTYPE") <*> argument Just (metavar "FILE")

    shouldSucceed tt file = do
      mbErr <- checkFile (testTypeCheckConf tt) file $ \_ -> return ()
      case mbErr of
        Left err -> do
          putStrLn $ PP.render $
            "Expecting success, but we got an error:" $$ PP.nest 2 err
          exitFailure
        Right _ -> do
          putStrLn "OK"


parseTest :: ParserInfo (IO ())
parseTest = info (helper <*> parseTest') fullDesc
