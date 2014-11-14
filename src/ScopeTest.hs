{-# LANGUAGE OverloadedStrings #-}
-- | Provides standalone scope checking of a file for debugging purposes
module ScopeTest(scopeCheckFile) where

import           Prelude                          hiding (interact)

import           Control.Monad.Trans.Except       (ExceptT(ExceptT), runExceptT)

import           PrettyPrint                      ((<+>), ($$))
import qualified PrettyPrint                      as PP
import           Prelude.Extended
import           Syntax


scopeCheckFile
  :: FilePath
  -> IO ()
scopeCheckFile file = do
  mbErr <- runExceptT $ do
      s   <- lift $ readFile file
      raw <- exceptShowErr "Parse" $ parseProgram s
      exceptShowErr "Scope" $ scopeCheckProgram raw
  case mbErr of
    Left err -> putStrLn $ "Scope check failed : " ++ show err 
    Right _ -> putStrLn "Scope check successful"
  where
    showError errType err =
      PP.text errType <+> "error: " $$ PP.nest 2 err

    exceptShowErr errType =
      ExceptT . return . either (Left . showError errType) Right
