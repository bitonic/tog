-- | Global configuration, what we get from the command line.  Every
-- program using tog as a library should start with @'writeConf' conf@.
module Tog.Instrumentation.Conf
  ( Conf(..)
  , confDebug
  , confDisableDebug
  , DebugLabels(..)
  , defaultConf
  , writeConf
  , readConf
  ) where

import           System.IO.Unsafe                 (unsafePerformIO)
import           Data.IORef                       (IORef, newIORef, atomicModifyIORef', readIORef)

import           Tog.Prelude

-- Configuration
------------------------------------------------------------------------

data Conf = Conf
  { confTermType                :: String
  , confSolver                  :: String
  , confDebugLabels             :: DebugLabels
  , confStackTrace              :: Bool
  , confQuiet                   :: Bool
  , confNoMetasSummary          :: Bool
  , confMetasReport             :: Bool
  , confMetasOnlyUnsolved       :: Bool
  , confNoProblemsSummary       :: Bool
  , confProblemsReport          :: Bool
  , confCheckMetaConsistency    :: Bool
  , confFastGetAbsName          :: Bool
  , confDisableSynEquality      :: Bool
  , confDontNormalizePP         :: Bool
  , confWhnfApplySubst          :: Bool
  , confTimeSections            :: Bool
  , confWhnfEliminate           :: Bool
  }

data DebugLabels
  = DLAll
  | DLSome [String]

confDebug :: Conf -> Bool
confDebug conf = case confDebugLabels conf of
  DLAll     -> True
  DLSome [] -> False
  DLSome _  -> True

confDisableDebug :: Conf -> Conf
confDisableDebug conf = conf{confDebugLabels = DLSome []}

instance Monoid DebugLabels where
  mempty = DLSome []

  DLAll     `mappend` _         = DLAll
  _         `mappend` DLAll     = DLAll
  DLSome xs `mappend` DLSome ys = DLSome (xs ++ ys)

defaultConf :: Conf
defaultConf = Conf "S" "Simple" mempty False False False False False False False False False False False False False False

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
