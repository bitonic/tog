-- | Solves unification problems.
module Tog.Unify
  ( SolveState
  , initSolveState
  , solve
  ) where

import           Tog.Instrumentation
import           Tog.Prelude
import           Tog.Term
import           Tog.Monad
import           Tog.Elaborate
import qualified Tog.Unify.Simple                 as Simple

data SolveState t = forall solveState. (PrettyM t (solveState t)) => SolveState
  { sState :: solveState t
  , sSolve :: forall r. Constraint t -> TC t r (solveState t) ()
  }

initSolveState :: (IsTerm t) => IO (SolveState t)
initSolveState = do
  solver <- confSolver <$> readConf
  case solver of
    "S" ->
      return $ SolveState{ sState = Simple.initSolveState
                         , sSolve = Simple.solve
                         }
    _ ->
      error $ "Unsupported solver " ++ solver

solve :: (IsTerm t) => Constraint t -> TC t r (SolveState t) ()
solve c = do
  SolveState ss solve' <- get
  ss' <- magnifyStateTC (const ss) $ solve' c >> get
  put $ SolveState ss' solve'

instance PrettyM t (SolveState t) where
  prettyM (SolveState ss _) = prettyM ss

