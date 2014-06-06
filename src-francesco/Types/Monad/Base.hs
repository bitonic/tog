module Types.Monad.Base
    ( -- * Monad definition
      TC
    , ClosedTC
    , TCState
    , TCErr(..)
    , initTCState
    , runTC
    , TCReport(..)
    , tcReport
      -- * Errors
    , typeError
      -- * Source location
    , atSrcLoc
      -- * Signature
    , getSignature
    , putSignature
      -- * Context
    , askContext
    , localContext
      -- * Problem handling
    , ProblemId
    , Stuck(..)
    , StuckTC
    , newProblem
    , bindProblem
    , waitOnProblem
    , solveProblems
    ) where

import Prelude                                    hiding (abs, pi)

import           Control.Applicative              (Applicative(pure, (<*>)))
import           Data.Void                        (Void)
import qualified Data.Map.Strict                  as Map
import qualified Data.Set                         as Set
import           Data.Typeable                    (Typeable, typeRep)
import           Data.Dynamic                     (Dynamic, toDyn, fromDynamic)
import           Control.Monad                    (ap, void, msum, when, forM, guard)
import           Data.Functor                     ((<$>), (<$))

import           Syntax.Abstract                  (SrcLoc, noSrcLoc, HasSrcLoc, srcLoc)
import           Syntax.Abstract.Pretty           ()
import qualified Types.Context                    as Ctx
import qualified Types.Signature                  as Sig
import           Types.Var
import           Types.Term

import Data.Proxy (Proxy(..))
import           Debug.Trace                      (trace)

-- Monad definition
------------------------------------------------------------------------

newtype TC t v a = TC {unTC :: (TCEnv t v, TCState t) -> TCRes t a}
  deriving (Functor)

data TCRes t a
  = OK (TCState t) a
  | Error TCErr
  deriving (Functor)

instance Applicative (TC t v) where
  pure  = return
  (<*>) = ap

instance Monad (TC t v) where
  return x = TC $ \(_, ts) -> OK ts x

  TC m >>= f =
    TC $ \s@(te, _) -> case m s of
      OK ts x   -> unTC (f x) (te, ts)
      Error err -> Error err

type ClosedTC t = TC t Void

runTC :: TCState t -> ClosedTC t a -> IO (Either TCErr (a, TCState t))
runTC ts (TC m) = return $ case m (initEnv, ts) of
  OK ts' x  -> Right (x, ts')
  Error err -> Left err

local :: (TCEnv t v -> TCEnv t v') -> TC t v' a -> TC t v a
local f (TC m) = TC $ \(te, ts) -> m (f te, ts)

modify :: (TCState t -> (TCState t, a)) -> TC t v a
modify f = TC $ \(_, ts) -> let (ts', x) = f ts in OK ts' x

modify_ :: (TCState t -> TCState t) -> TC t v ()
modify_ f = modify $ \ts -> (f ts, ())

get :: TC t v (TCState t)
get = modify $ \ts -> (ts, ts)

data TCEnv t v = TCEnv
    { teContext       :: !(Ctx.ClosedCtx t v)
    , teCurrentSrcLoc :: !SrcLoc
    }

initEnv :: Closed (TCEnv t)
initEnv = TCEnv
  { teContext       = Ctx.Empty
  , teCurrentSrcLoc = noSrcLoc
  }

data TCState t = TCState
    { tsSignature          :: !(Sig.Signature t)
    , tsProblems           :: !(Map.Map ProblemIdInt (Problem t))
    , tsSolvedProblems     :: !(Map.Map ProblemIdInt SolvedProblem)
    }

initTCState :: TCState t
initTCState = TCState
  { tsSignature          = Sig.empty
  , tsProblems           = Map.empty
  , tsSolvedProblems     = Map.empty
  }

data TCErr
    = StrErr SrcLoc String

instance Show TCErr where
  show (StrErr p s) =
    "Error at " ++ show p ++ ":\n" ++ unlines (map ("  " ++) (lines s))

data TCReport t = TCReport
  { trSignature        :: !(Sig.Signature t)
  , trSolvedProblems   :: !Int
  , trUnsolvedProblems :: !Int
  }

tcReport :: TCState t -> TCReport t
tcReport ts = TCReport
  { trSignature        = tsSignature ts
  , trSolvedProblems   = Map.size $ tsSolvedProblems ts
  , trUnsolvedProblems = Map.size $ tsProblems ts
  }

-- Errors
------------------------------------------------------------------------

typeError :: String -> TC t v b
typeError err = TC $ \(te, _) -> Error $ StrErr (teCurrentSrcLoc te) err

-- SrcLoc
------------------------------------------------------------------------

atSrcLoc :: HasSrcLoc a => a -> TC t v b -> TC t v b
atSrcLoc x = local $ \te -> te{teCurrentSrcLoc = srcLoc x}

-- Signature
------------------------------------------------------------------------

-- Basics
---------

getSignature :: TC t v (Sig.Signature t)
getSignature = modify $ \ts -> (ts, tsSignature ts)

putSignature :: Sig.Signature t -> TC t v ()
putSignature sig = modify_ $ \ts -> ts{tsSignature = sig}

-- Context
------------------------------------------------------------------------

askContext :: TC t v (Ctx.ClosedCtx t v)
askContext = TC $ \(te, ts) -> OK ts $ teContext te

localContext
    :: (Ctx.ClosedCtx t v -> Ctx.ClosedCtx t v') -> TC t v' a -> TC t v a
localContext f = local $ \env -> env{teContext = f (teContext env)}

-- Problem handling
------------------------------------------------------------------------

type ProblemIdInt = Int

newtype ProblemId (t :: * -> *) v a = ProblemId ProblemIdInt

data Problem t = forall a b v. (Typeable a, Typeable b, Typeable v) => Problem
    { pContext :: !(Ctx.ClosedCtx t v)
    , pProblem :: !(a -> StuckTC t v b)
    , pState   :: !ProblemState
    }

data ProblemState
    = BoundToMetaVars  !(Set.Set MetaVar)
    | WaitingOnProblem !ProblemIdInt
    | BoundToProblem   !ProblemIdInt
    deriving (Show)

newtype SolvedProblem = SolvedProblem Dynamic

solvedProblem :: Typeable a => a -> SolvedProblem
solvedProblem = SolvedProblem . toDyn

data Stuck t v a
    = StuckOn (ProblemId t v a)
    | NotStuck a

type StuckTC t v a = TC t v (Stuck t v a)

saveSrcLoc :: Problem t -> TC t v (Problem t)
saveSrcLoc (Problem ctx m st) = do
  loc <- TC $ \(te, ts) -> OK ts $ teCurrentSrcLoc te
  return $ Problem ctx (\x -> atSrcLoc loc (m x)) st

addProblem :: Problem t -> TC t v (ProblemId t v a)
addProblem prob = do
  modify $ \ts ->
    let probs = tsProblems ts
        pid = case Map.maxViewWithKey probs of
                Nothing             -> 0
                Just ((pid0, _), _) -> pid0 + 1
    in (ts{tsProblems = Map.insert pid prob probs}, ProblemId pid)

newProblem
    :: (Typeable a, Typeable v, Typeable t)
    => Set.Set MetaVar -> (Closed (Term t) -> StuckTC t v a) -> TC t v (ProblemId t v a)
newProblem mvs m = do
    ctx <- askContext
    prob <- saveSrcLoc $ Problem
      { pContext = ctx
      , pProblem = m
      , pState   = BoundToMetaVars mvs
      }
    addProblem prob

bindProblem
    :: (Typeable a, Typeable b, Typeable v)
    => ProblemId t v a -> (a -> StuckTC t v b) -> TC t v (ProblemId t v b)
bindProblem (ProblemId pid) f = do
    ctx <- askContext
    prob <- saveSrcLoc $ Problem
      { pContext = ctx
      , pProblem = f
      , pState   = BoundToProblem pid
      }
    addProblem prob

waitOnProblem
    :: (Typeable a, Typeable b, Typeable v')
    => ProblemId t v a -> StuckTC t v' b -> TC t v' (ProblemId t v' b)
waitOnProblem (ProblemId pid) m = do
    ctx <- askContext
    prob <- saveSrcLoc $ Problem
      { pContext = ctx
      , pProblem = \() -> m
      , pState   = WaitingOnProblem pid
      }
    addProblem prob

-- TODO improve efficiency of this.
solveProblems :: (Typeable t) => ClosedTC t ()
solveProblems = do
  unsolvedProbs <- Map.toList . tsProblems <$> get
  progress <- fmap or $ forM unsolvedProbs $ \(pid, (Problem ctx prob state)) -> do
    mbSolved <- case state of
      BoundToMetaVars mvs -> do
        sig <- getSignature
        let instantiatedMvs = Sig.instantiatedMetaVars sig
        let mbMv = msum [ mv <$ guard (Set.member mv instantiatedMvs)
                        | mv <- Set.toList mvs
                        ]
        case mbMv of
          Nothing -> do
            return Nothing
          Just mv -> do
            let Just mvBody = Sig.getMetaVarBody sig mv
            return $ Just $ solvedProblem mvBody
      BoundToProblem boundTo -> do
        Map.lookup boundTo . tsSolvedProblems <$> get
      WaitingOnProblem waitingOn -> do
        mbSolved <- Map.lookup waitingOn . tsSolvedProblems <$> get
        case mbSolved of
          Nothing -> return Nothing
          Just _  -> return $ Just $ solvedProblem ()
    case mbSolved of
      Nothing     -> return False
      Just solved -> do trace ("Solving problem " ++ show pid ++ " on " ++ show state) $ return ()
                        True <$ solveProblem pid solved ctx prob
  when progress solveProblems
  where
    solveProblem
      :: (Typeable a, Typeable b, Typeable v)
      => ProblemIdInt -> SolvedProblem
      -> Ctx.ClosedCtx t v -> (a -> StuckTC t v b)
      -> ClosedTC t ()
    solveProblem pid (SolvedProblem x) ctx (m :: a -> StuckTC t' v' b') = do
      trace ("Type of solved: " ++ show x) $ return ()
      trace ("Type of arg: " ++ show (typeRep (Proxy :: Proxy a))) $ return ()
      Just x' <- return $ fromDynamic x
      modify_ $ \ts -> ts{tsProblems = Map.delete pid (tsProblems ts)}
      localContext (\_ -> ctx) $ do
        stuck <- m x'
        case stuck of
          NotStuck y -> do
            trace ("=== Solved problem " ++ show pid) $ return ()
            -- Mark the problem as solved.
            modify_ $ \ts ->
              ts{tsSolvedProblems = Map.insert pid (solvedProblem y) (tsSolvedProblems ts)}
          StuckOn (ProblemId boundTo) -> do
            trace ("Stuck problem " ++ show pid ++ " on " ++ show pid) $ return ()
            -- If the problem is stuck, re-add it as a dependency of
            -- what it is stuck on.
            void $ addProblem $ Problem ctx m $ BoundToProblem boundTo
