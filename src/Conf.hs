module Conf (Conf(..), writeConf, readConf) where

import           Control.Monad                    (unless)
import           System.IO.Unsafe                 (unsafePerformIO)
import           Control.Concurrent.MVar          (MVar, newEmptyMVar, tryPutMVar, tryReadMVar)

-- Configuration
------------------------------------------------------------------------

data Conf = Conf
  { confTermType                :: String
  , confSolver                  :: String
  , confQuiet                   :: Bool
  , confNoMetaVarsSummary       :: Bool
  , confMetaVarsReport          :: Bool
  , confMetaVarsOnlyUnsolved    :: Bool
  , confNoProblemsSummary       :: Bool
  , confProblemsReport          :: Bool
  , confDebug                   :: Bool
  , confCheckMetaVarConsistency :: Bool
  , confFastGetAbsName          :: Bool
  , confDisableSynEquality      :: Bool
  , confNormalizePrettyPrinted  :: Bool
  }

{-# PRAGMA NOINLINE #-}
confRef :: MVar Conf
confRef = unsafePerformIO newEmptyMVar

writeConf :: Conf -> IO ()
writeConf conf = do
  ok <- tryPutMVar confRef conf
  unless ok $ error "writeConf: already written."

readConf :: IO Conf
readConf = do
  mbConf <- tryReadMVar confRef
  case mbConf of
    Nothing   -> error "readConf: conf not written"
    Just conf -> return conf
