-- | Global configuration, what we get from the command line.  Every
-- program using tog as a library should start with @'writeConf' conf@.
module Conf (Conf(..), defaultConf, writeConf, readConf) where

import           Control.Monad                    (unless)
import           System.IO.Unsafe                 (unsafePerformIO)
import           Control.Monad.IO.Class           (MonadIO, liftIO)
import           Data.IORef                       (IORef, newIORef, atomicModifyIORef', readIORef)

-- Configuration
------------------------------------------------------------------------

data Conf = Conf
  { confTermType                :: String
  , confSolver                  :: String
  , confDebugLabels             :: [(Bool, [String])]
  , confStackTrace              :: Bool
  , confQuiet                   :: Bool
  , confNoMetaVarsSummary       :: Bool
  , confMetaVarsReport          :: Bool
  , confMetaVarsOnlyUnsolved    :: Bool
  , confNoProblemsSummary       :: Bool
  , confProblemsReport          :: Bool
  , confCheckMetaVarConsistency :: Bool
  , confFastGetAbsName          :: Bool
  , confDisableSynEquality      :: Bool
  , confDontNormalizePP         :: Bool
  , confWhnfApplySubst          :: Bool
  }

defaultConf :: Conf
defaultConf = Conf "S" "Simple" [] False False False False False False False False False False False False

{-# NOINLINE confRef #-}
confRef :: IORef (Maybe Conf)
confRef = unsafePerformIO $ newIORef Nothing

writeConf :: (MonadIO m) => Conf -> m ()
writeConf conf = do
  ok <- liftIO $ atomicModifyIORef' confRef $ \mbConf -> case mbConf of
    Nothing -> (Just conf, True)
    Just c  -> (Just c,    False)
  unless ok $ error "writeConf: already written."

readConf :: (MonadIO m) => m Conf
readConf = do
  mbConf <- liftIO $ readIORef confRef
  case mbConf of
    Nothing   -> error "readConf: conf not written"
    Just conf -> return conf
