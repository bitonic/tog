{-# LANGUAGE OverloadedStrings #-}
module TypeCheck.Monad
  ( -- * Monad definition
    TC
  , TCState
  , tcState
  , TCErr(..)
  , initTCState
  , runTC
    -- * Report
  , TCReport(..)
  , tcReport
    -- * Operations
    -- ** Errors
  , typeError
  , assert
    -- ** Source location
  , atSrcLoc
    -- ** 'TermM'
  , liftTermM
    -- ** Using the 'Signature'
  , withSignature
  , withSignatureTermM
    -- ** Definition handling
  , addDefinition
  , addDefinitionSynthetic
  , getDefinition
  , getDefinitionSynthetic
  , addConstant
  , addDataCon
  , addProjection
  , addClauses
    -- ** MetaVar handling
  , addMetaVar
  , instantiateMetaVar
  , getMetaVarType
  , getMetaVarBody
    -- * Debugging
  , enableDebug
  , disableDebug
  , debugBracket
  , debugBracket_
  , debug
    -- * State
  , getState
  , putState
    -- * Problem handling
  , ProblemId
  , ProblemIdInt
  , ProblemState
  , Stuck(..)
  , newProblem
  , newProblem_
  , bindProblem
  , solveProblems
  , solveProblems_
    -- ** StuckTC
  , StuckTC
  , returnStuckTC
  , bindStuckTC
  ) where

import qualified Data.HashMap.Strict              as HMS
import qualified Data.HashSet                     as HS
import           System.IO                        (hPutStr, stderr)
import           Unsafe.Coerce                    (unsafeCoerce)

import           Prelude.Extended
import           Syntax.Internal                  (Name, SrcLoc, noSrcLoc, HasSrcLoc, srcLoc, DefName(SimpleName))
import           Term
import qualified Term.Signature                   as Sig
import qualified Term.Telescope                   as Tel
import           Text.PrettyPrint.Extended        ((<+>), ($$))
import qualified Text.PrettyPrint.Extended        as PP

-- Monad definition
------------------------------------------------------------------------

-- | The "type checking" monad.
--
-- It carries around a signature, that we can modify
-- ('modifySignature'), It also lets you track of the current location
-- in the source code.
--
-- Moreover, it lets us suspend computations waiting on a 'MetaVar' to
-- be instantiated, or on another suspended computation to be completed.
-- See 'ProblemId' and related functions.
newtype TC t p s a = TC {unTC :: (TCEnv t p s, TCState t p s) -> IO (TCRes t p s a)}
  deriving (Functor)

data TCRes t p s a
  = OK (TCState t p s) a
  | Error TCErr
  deriving (Functor)

instance Applicative (TC t p s) where
  pure  = return
  (<*>) = ap

instance Monad (TC t p s) where
  return x = TC $ \(_, ts) -> return $ OK ts x

  TC m >>= f =
    TC $ \s@(loc, _) -> do
      res <- m s
      case res of
        OK ts x   -> unTC (f x) (loc, ts)
        Error err -> return $ Error err

-- | Takes a 'TCState' and a computation on a closed context and
-- produces an error or a result with a new state.
runTC :: InterpretProblem t p s -> TCState t p s
      -> TC t p s a -> IO (Either PP.Doc (a, TCState t p s))
runTC int ts (TC m) = do
  res <- m (initEnv int, ts)
  return $ case res of
    OK ts' x  -> Right (x, ts')
    Error err -> Left $ PP.pretty err

data TCEnv t p s = TCEnv
    { teCurrentSrcLoc    :: !SrcLoc
    , teInterpretProblem :: !(InterpretProblem t p s)
    , teDebug            :: !Bool
    , teDebugDepth       :: !Int
    }

initEnv :: InterpretProblem t p s -> TCEnv t p s
initEnv int =
  TCEnv{ teCurrentSrcLoc    = noSrcLoc
       , teInterpretProblem = int
       , teDebug            = False
       , teDebugDepth       = 0
       }

data TCState t p s = TCState
    { tsSignature        :: !(Sig.Signature t)
    , tsUnsolvedProblems :: !(HMS.HashMap ProblemIdInt (Problem p))
    , tsSolvedProblems   :: !(HMS.HashMap ProblemIdInt ProblemSolution)
    , tsProblemCount     :: !Int
    , tsState            :: !s
    }

-- | An empty state.
initTCState
  :: s -> TCState t p s
initTCState s = TCState
  { tsSignature        = Sig.empty
  , tsUnsolvedProblems = HMS.empty
  , tsSolvedProblems   = HMS.empty
  , tsProblemCount     = 0
  , tsState            = s
  }

tcState :: TCState t p s -> s
tcState = tsState

data TCErr
    = DocErr SrcLoc PP.Doc

instance PP.Pretty TCErr where
  pretty (DocErr p s) =
    "Error at" <+> PP.text (show p) <+> ":" $$
    PP.nest 2 s

instance Show TCErr where
  show = PP.render

-- TCReport
------------------------------------------------------------------------

-- | A type useful to inspect what's going on.
data TCReport t p = TCReport
  { trSignature        :: !(Sig.Signature t)
  , trSolvedProblems   :: !(HS.HashSet ProblemIdInt)
  , trUnsolvedProblems :: !(HMS.HashMap ProblemIdInt (Problem p))
  }

tcReport :: (IsTerm t) => TCState t p s -> TCReport t p
tcReport ts = TCReport
  { trSignature        = sig
  , trSolvedProblems   = HS.fromList $ HMS.keys $ tsSolvedProblems ts
  , trUnsolvedProblems = tsUnsolvedProblems ts
  }
  where
    sig = tsSignature ts

-- Errors
------------------------------------------------------------------------

-- | Fail with an error message.
typeError :: PP.Doc -> TC t p s b
typeError err = TC $ \(te, _) -> return $ Error $ DocErr (teCurrentSrcLoc te) err

assert :: (PP.Doc -> String) -> TC t p s a -> TC t p s a
assert msg (TC m) = TC $ \(te, ts) -> do
  res <- m (te, ts)
  case res of
    Error (DocErr _ err) -> error $ msg err
    OK ts' x             -> return $ OK ts' x

-- SrcLoc
------------------------------------------------------------------------

-- | Run some action with the given 'SrcLoc'.
atSrcLoc :: HasSrcLoc a => a -> TC t p s b -> TC t p s b
atSrcLoc x (TC m) = TC $ \(te, ts) -> m (te{teCurrentSrcLoc = srcLoc x}, ts)

-- TermM
------------------------------------------------------------------------

liftTermM :: TermM a -> TC t p s a
liftTermM m = TC $ \(_, ts) -> do
  x <- m
  return $ OK ts x

-- Signature
------------------------------------------------------------------------

-- | Do something with the current signature.
withSignature :: (Sig.Signature t -> a) -> TC t p s a
withSignature f = do
  sig <- modify $ \ts -> (ts, tsSignature ts)
  return $ f sig

withSignatureTermM :: (Sig.Signature t -> TermM a) -> TC t p s a
withSignatureTermM f = do
  sig <- modify $ \ts -> (ts, tsSignature ts)
  liftTermM $ f sig

getDefinition
  :: (IsTerm t) => Name -> TC t p s (Closed (Definition t))
getDefinition n = getDefinitionSynthetic (SimpleName n)

getDefinitionSynthetic
  :: (IsTerm t) => DefName -> TC t p s (Closed (Definition t))
getDefinitionSynthetic n = do
  sig <- tsSignature <$> get
  return $ Sig.getDefinition sig n

addDefinition'
  :: (IsTerm t) => DefName -> Closed (Definition t) -> TC t p s ()
addDefinition' n def' =
  modify_ $ \ts -> ts{tsSignature = Sig.addDefinition (tsSignature ts) n def'}

addDefinition
  :: (IsTerm t) => Name -> Closed (Definition t) -> TC t p s ()
addDefinition n = addDefinition' (SimpleName n)

addDefinitionSynthetic
  :: (IsTerm t) => Name -> Closed (Definition t) -> TC t p s DefName
addDefinitionSynthetic n def' =
  modify $ \ts ->
    let (dn, sig') = Sig.addDefinitionSynthetic (tsSignature ts) n def'
    in (ts{tsSignature = sig'}, dn)

addConstant
    :: (IsTerm t)
    => Name -> ConstantKind -> Closed (Type t) -> TC t p s ()
addConstant x k a = addDefinition x (Constant k a)

addDataCon
    :: (IsTerm t)
    => Name -> Name -> Tel.Tel (Type t) -> Type t -> TC t p s ()
addDataCon c d tel t = addDefinition c (DataCon d tel t)

addProjection
    :: (IsTerm t)
    => Name -> Field -> Name -> Tel.Tel (Type t) -> Type t -> TC t p s ()
addProjection f n r tel t = addDefinition f (Projection n r tel t)

addClauses
    :: (IsTerm t) => DefName -> Closed (Invertible t) -> TC t p s ()
addClauses f clauses = do
  def' <- getDefinitionSynthetic f
  let ext (Constant Postulate a) = return $ Function a clauses
      ext (Function _ _)         = error $ "TC.addClause: clause `" ++ show f ++ "' already added."
      ext (Constant k _)         = error $ "TC.addClause: constant `" ++ show k ++ "'"
      ext DataCon{}              = error $ "TC.addClause: constructor"
      ext Projection{}           = error $ "TC.addClause: projection"
  addDefinition' f =<< ext def'

addMetaVar :: (IsTerm t) => Closed (Type t) -> TC t p s MetaVar
addMetaVar type_ = do
  sig <- tsSignature <$> get
  let (mv, sig') = Sig.addMetaVar sig type_
  modify_ $ \ts -> ts{tsSignature = sig'}
  return mv

instantiateMetaVar
  :: (IsTerm t) => MetaVar -> Closed (Term t) -> TC t p s ()
instantiateMetaVar mv t = do
  modify_ $ \ts -> ts{tsSignature = Sig.instantiateMetaVar (tsSignature ts) mv t}

getMetaVarType
  :: (IsTerm t) => MetaVar -> TC t p s (Closed (Type t))
getMetaVarType mv = do
  sig <- tsSignature <$> get
  return $ Sig.getMetaVarType sig mv

getMetaVarBody
  :: (IsTerm t) => MetaVar -> TC t p s (Maybe (Closed (Term t)))
getMetaVarBody mv = do
  sig <- tsSignature <$> get
  return $ Sig.getMetaVarBody sig mv

-- Debugging
------------------------------------------------------------------------

enableDebug :: TC t p s a -> TC t p s a
enableDebug (TC m) = TC $ \(te, ts) -> m (te{teDebug = True}, ts)

disableDebug :: TC t p s a -> TC t p s a
disableDebug (TC m) = TC $ \(te, ts) -> m (te{teDebug = False}, ts)

debugBracket :: TC t p s PP.Doc -> TC t p s a -> TC t p s a
debugBracket docM m = do
  doc' <- docM'
  debug doc'
  te <- ask
  local te{teDebugDepth = teDebugDepth te + 1} m
  where
    docM' = TC $ \(te, ts) -> do
      mbDoc <- unTC docM (te, ts)
      case mbDoc of
        OK ts' doc' ->
          return $ OK ts' doc'
        Error (DocErr _ err) -> do
          error $ PP.render $ "debugBracket: the doc action got an error:" $$ err

debugBracket_ :: PP.Doc -> TC t p s a -> TC t p s a
debugBracket_ doc = debugBracket (return doc)

debug :: PP.Doc -> TC t p s ()
debug doc = TC $ \(te, ts) -> do
  when (teDebug te) $ do
    let s  = PP.renderStyle PP.style{PP.lineLength = 300} doc
    let pad = replicate (teDebugDepth te * 2) ' '
    hPutStr stderr $ unlines $ map (pad ++) $ lines s
  return $ OK ts ()

-- State
------------------------------------------------------------------------

getState :: TC t p s s
getState = TC $ \(_, ts) -> do
  return $ OK ts $ tsState $ ts

putState :: s -> TC t p s ()
putState s = TC $ \(_, ts) -> do
  return $ OK ts{tsState = s} ()

-- Problem handling
------------------------------------------------------------------------

-- | An 'Int' version of the 'ProblemId', useful for debugging (see
-- 'TCReport').
type ProblemIdInt = Int

-- | A 'ProblemId' identifies a suspended computation and carries around
-- the type of the result of the computation it refers to.
newtype ProblemId a = ProblemId ProblemIdInt
  deriving (Show)

-- | To store problems, we store the context of the suspended
-- computation; and its state and description living in said context.
--
-- Both the type of the bound variable and the result type are
-- 'Typeable' since we store the solutions and problems dynamically so
-- that they can all be in the same 'HMS.HashMap'.
data Problem p = forall a b. Problem
  { pProblem :: !(Maybe (p a b))
    -- ^ If 'Nothing', it means that we're just waiting on another
    -- problem to complete and we'll then return its result.
  , pState   :: !ProblemState
  , pSrcLoc  :: !SrcLoc
  }

type InterpretProblem t p s =
  forall a b. p a b -> a -> StuckTC t p s b

data ProblemState
    = BoundToMetaVars  !(HS.HashSet MetaVar)
    | BoundToProblem   !ProblemIdInt
    deriving (Show)

instance PP.Pretty ProblemState where
  pretty (BoundToMetaVars mvs)  = "BoundToMetaVars" <+> PP.pretty (HS.toList mvs)
  pretty (BoundToProblem pid)   = "BoundToProblem" <+> PP.pretty pid

-- | As remarked, we store the problems solutions dynamically to have
-- them in a single 'HMS.HashMap'.
data ProblemSolution = forall a. ProblemSolution a

problemSolution :: a -> ProblemSolution
problemSolution = ProblemSolution

-- | Datatype useful to represent computations that might return a
-- result directly or the 'ProblemId' of a problem containing the
-- result.
data Stuck a
    = StuckOn (ProblemId a)
    | NotStuck a

addProblem :: ProblemIdInt -> Problem p -> TC t p s (ProblemId a)
addProblem pid prob = do
  modify $ \ts -> (ts{tsUnsolvedProblems = HMS.insert pid prob (tsUnsolvedProblems ts)}, ProblemId pid)

addFreshProblem :: Problem p -> TC t p s (ProblemId a)
addFreshProblem prob = do
  pid <- modify $ \ts ->
         let count = tsProblemCount ts in (ts{tsProblemCount = count + 1}, count)
  addProblem pid prob

-- | Store a new problem dependend on a set of 'MetaVar's.  When one of
-- them will be instantiated, the computation can be executed again.
newProblem
    :: HS.HashSet MetaVar
    -> p () b
    -> StuckTC t p s b
newProblem mvs m = do
    loc <- teCurrentSrcLoc <$> ask
    let prob = Problem{pProblem = Just m, pState = BoundToMetaVars mvs, pSrcLoc = loc}
    StuckOn <$> addFreshProblem prob

newProblem_
    :: MetaVar
    -> p () b
    -> StuckTC t p s b
newProblem_ mv = newProblem (HS.singleton mv)

-- | @bindProblem pid desc (\x -> m)@ binds computation @m@ to problem
-- @pid@. When @pid@ is solved with result @t@, @m t@ will be executed.
bindProblem
    :: ProblemId a
    -> (p a b)
    -> StuckTC t p s b
bindProblem (ProblemId pid) f = do
    loc <- teCurrentSrcLoc <$> ask
    let prob = Problem{pProblem = Just f, pState = BoundToProblem pid, pSrcLoc = loc}
    StuckOn <$> addFreshProblem prob

-- | This computation solves all problems that are solvable in the
-- current state.  Returns whether any problem was solved.
solveProblems :: forall p t s. TC t p s Bool
solveProblems = do
  unsolvedProbs <- HMS.toList . tsUnsolvedProblems <$> get
  -- Go over all unsolved problems and record if we made progress in any
  -- of them.
  progress <- fmap or $ forM unsolvedProbs $ \(pid, (Problem prob state loc)) -> do
    -- Collect the state necessary to execute the current problem, if
    -- available.
    mbSolution :: Maybe ProblemSolution <- case state of
      -- If we're waiting on metavars, check if at least one is
      -- instantiated.  The state will be ().
      BoundToMetaVars mvs -> do
        withSignature $ \sig -> msum
          [ problemSolution () <$ HMS.lookup mv (Sig.metaVarsBodies sig)
          | mv <- HS.toList mvs
          ]
      -- If we're bound to another problem, retrieve its result if
      -- available.
      BoundToProblem boundTo ->
        HMS.lookup boundTo . tsSolvedProblems <$> get
    case mbSolution of
      Nothing       -> return False
      Just solution -> True <$ solveProblem pid prob loc solution
  progress <$ when progress (void solveProblems)
  where
    solveProblem
      :: forall a b.
         ProblemIdInt
      -- ^ pid of the problem we're solving.
      -> Maybe (p a b)
      -- ^ ...and the suspended computation, if present.
      -> SrcLoc
      -- ^ ...and 'SrcLoc' of the problem.
      -> ProblemSolution
      -- ^ Solution to the problem we were waiting on.
      -> TC t p s ()
    solveProblem pid mbP loc (ProblemSolution x) = do
      -- Delete the problem from the list of unsolved problems.
      modify_ $ \ts -> ts{tsUnsolvedProblems = HMS.delete pid (tsUnsolvedProblems ts)}
      -- Execute the suspended computation. From how the functions
      -- adding problems are designed we know that the types will match
      -- up.
      stuck <- case mbP of
        Nothing -> do
          -- TODO replace with something safe, for example using :~:.
          -- Same below.
          let Just x' = Just $ unsafeCoerce x
          return $ NotStuck x'
        Just p  -> do
          let Just x' = Just $ unsafeCoerce x
          comp <- teInterpretProblem <$> ask
          atSrcLoc loc $ debugBracket_ ("*** Resuming problem" <+> PP.pretty pid) $
            comp p x'
      case stuck of
        NotStuck y -> do
          -- Mark the problem as solved.
          modify_ $ \ts ->
            ts{tsSolvedProblems = HMS.insert pid (problemSolution y) (tsSolvedProblems ts)}
        StuckOn (ProblemId boundTo) -> do
          -- If the problem is stuck, re-add it as a dependency of
          -- what it is stuck on.
          void $ addProblem pid $
            Problem (Nothing :: Maybe (p a b)) (BoundToProblem boundTo) loc
          return ()

solveProblems_ :: TC t p s ()
solveProblems_ = void solveProblems

-- StuckTC
----------

type StuckTC p t s a = TC p t s (Stuck a)

returnStuckTC :: a -> StuckTC p t s a
returnStuckTC = return . NotStuck

infixl 2 `bindStuckTC`

bindStuckTC
  :: StuckTC t p s a -> p a b -> StuckTC t p s b
bindStuckTC m p = do
  stuck <- m
  case stuck of
    NotStuck x -> do
      int <- teInterpretProblem <$> ask
      int p x
    StuckOn pid ->
      bindProblem pid p

-- Utils
------------------------------------------------------------------------

modify :: (TCState t p s -> (TCState t p s, a)) -> TC t p s a
modify f = TC $ \(_, ts) -> let (ts', x) = f ts in return $ OK ts' x

modify_ :: (TCState t p s -> TCState t p s) -> TC t p s ()
modify_ f = modify $ \ts -> (f ts, ())

get :: TC t p s (TCState t p s)
get = modify $ \ts -> (ts, ts)

ask :: TC t p s (TCEnv t p s)
ask = TC $ \(te, ts) -> return $ OK ts te

local :: TCEnv t p s -> TC t p s a -> TC t p s a
local te (TC m) = TC $ \(_, ts) -> m (te, ts)
