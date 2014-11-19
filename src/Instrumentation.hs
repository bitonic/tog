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
  , stackTrace
    -- * Init
  , instrument
  ) where

import           Control.Exception                (bracket)

import           Instrumentation.Debug
import           Instrumentation.Timing
import           Instrumentation.Conf
import           Prelude.Extended

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
