module Tog.Instrumentation
  ( -- * Conf
    module Tog.Instrumentation.Conf
    -- * Debug
  , DebugLabel
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

import           Tog.Instrumentation.Debug
import           Tog.Instrumentation.Timing
import           Tog.Instrumentation.Conf
import           Tog.Prelude

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
