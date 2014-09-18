module TypeCheck3.Solve
  ( SolveState
  , initSolveState
  , solve
  , prettySolveState
  , prettySolveStateTC
  ) where

import           Control.Monad.State.Class        (get)

import           Term
import qualified PrettyPrint                      as PP
import           TypeCheck3.Monad

import           TypeCheck3.Solve.Simple
import           TypeCheck3.Solve.TwoContexts ()

prettySolveStateTC
  :: (IsTerm t) => Bool -> TC t (SolveState t) PP.Doc
prettySolveStateTC detailed = do
  s <- get
  withSignatureTermM $ \sig -> prettySolveState sig detailed s
