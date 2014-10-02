module Conf (Conf(..), defaultConf, writeConf, readConf) where

import           Control.Monad                    (unless)
import           System.IO.Unsafe                 (unsafePerformIO)
import           Control.Concurrent.MVar          (MVar, newEmptyMVar, tryPutMVar, tryReadMVar)
import           Control.Monad.IO.Class           (MonadIO, liftIO)

-- Configuration
------------------------------------------------------------------------

data Conf = Conf
  { confTermType                :: String
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
  , confDontNormalizePP         :: Bool
  }

defaultConf :: Conf
defaultConf = Conf "S" False False False False False False False False False False False

{-# NOINLINE confRef #-}
confRef :: MVar Conf
confRef = unsafePerformIO newEmptyMVar

writeConf :: (MonadIO m) => Conf -> m ()
writeConf conf = do
  ok <- liftIO $ tryPutMVar confRef conf
  unless ok $ error "writeConf: already written."
    
readConf :: (MonadIO m) => m Conf
readConf = do
  mbConf <- liftIO $ tryReadMVar confRef
  case mbConf of
    Nothing   -> error "readConf: conf not written"
    Just conf -> return conf
