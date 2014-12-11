module Instrumentation
  ( -- * Conf
    module Instrumentation.Conf
    -- * Debug
  , debugBracket
  , debugBracket_
  , debug
  , debug_
  , whenDebug
  , fatalError
  , printStackTrace
    -- * Init
  , instrument
  ) where

import           Control.Exception                (bracket)

import           Instrumentation.Debug
import           Instrumentation.Timing
import           Instrumentation.Conf
import           TogPrelude

instrument :: Conf -> IO a -> IO a
instrument conf m = bracket init' (\() -> halt) (\() -> m)
  where
    init' = do
      writeConf conf
      timingInit
      debugInit

    halt = do
      timing <- confTimeSections `liftM` readConf
      when timing timingReport
