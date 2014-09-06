{-# LANGUAGE OverloadedStrings #-}
module TypeCheck2.Monad
  ( -- * Monad definition
    TC
  , TCState
  , tcState
  , TCErr(..)
  , initTCState
  , runTC
  , catchTC
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
  , getDefinition
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
  , debug_
    -- * State
  , getState
  , putState
    -- * Problem handling
  , ProblemId
  , unProblemId
  , ProblemIdInt
  , ProblemState(..)
  , Problem(..)
  , Stuck(..)
  , notStuck
  , stuckOn
  , WaitingOn(..)
  , newProblem
  , bindProblem
  , solveProblems
  , solveProblems_
  , catchProblem
    -- ** StuckTC
  , StuckTC
  , returnStuckTC
  , bindStuckTC
    -- * Freezing
  , freeze
  ) where

import qualified Data.HashMap.Strict              as HMS
import qualified Data.HashSet                     as HS
import qualified Data.Map.Strict                  as Map
import           System.IO                        (hPutStr, stderr)
import           Unsafe.Coerce                    (unsafeCoerce)

import           Prelude.Extended
import           PrettyPrint                      ((<+>), ($$), (//>))
import qualified PrettyPrint                      as PP
import           Syntax.Internal                  (Name, SrcLoc, noSrcLoc, HasSrcLoc, srcLoc, MetaVar)
import           Term
import qualified Term.Signature                   as Sig
import qualified Term.Telescope                   as Tel

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

catchTC
  :: (IsTerm t)
  => TC t p s a -> TC t p s (Either TCErr a)
catchTC m = TC $ \(te, ts) -> do
  res <- unTC m (te, ts)
  case res of
    OK ts' x  -> return $ OK ts' $ Right x
    Error err -> return $ OK ts  $ Left err

-- | Takes a 'TCState' and a computation on a closed context and
-- produces an error or a result with a new state.
runTC :: (IsTerm t)
      => InterpretProblem t p s -> DescribeProblem t p s
      -> TCState t p s
      -> TC t p s a -> IO (Either PP.Doc (a, TCState t p s))
runTC int desc ts (TC m) = do
  res <- m (initEnv int desc, ts)
  return $ case res of
    OK ts' x  -> Right (x, ts')
    Error err -> Left $ PP.pretty err

data TCEnv t p s = TCEnv
    { teCurrentSrcLoc    :: !SrcLoc
    , teInterpretProblem :: !(InterpretProblem t p s)
    , teDescribeProblem  :: !(DescribeProblem t p s)
    , teDebug            :: !(Maybe Debug)
    , teFrozen           :: !Bool
    }

data Debug = Debug
  { dDepth      :: !Int
  , dStackTrace :: ![PP.Doc]
  }

initDebug :: Debug
initDebug = Debug 0 []

initEnv :: InterpretProblem t p s -> DescribeProblem t p s -> TCEnv t p s
initEnv int desc =
  TCEnv{ teCurrentSrcLoc    = noSrcLoc
       , teInterpretProblem = int
       , teDescribeProblem  = desc
       , teDebug            = Nothing
       , teFrozen           = False
       }

data TCState t p s = TCState
    { tsSignature        :: !(Sig.Signature t)
    , tsUnsolvedProblems :: !(Map.Map ProblemIdInt (Problem p))
    , tsSolvedProblems   :: !(HMS.HashMap ProblemIdInt ProblemSolution)
    , tsProblemCount     :: !Int
    , tsCatchProblem     :: !Bool
    , tsState            :: !s
    }

-- | An empty state.
initTCState
  :: s -> TCState t p s
initTCState s = TCState
  { tsSignature        = Sig.empty
  , tsUnsolvedProblems = Map.empty
  , tsSolvedProblems   = HMS.empty
  , tsProblemCount     = 0
  , tsCatchProblem     = False
  , tsState            = s
  }

tcState :: TCState t p s -> s
tcState = tsState

data TCErr
    = DocErr SrcLoc PP.Doc
    | CatchProblem ProblemState

instance PP.Pretty TCErr where
  pretty (DocErr p s) =
    "Error at" <+> PP.text (show p) <+> ":" $$
    PP.nest 2 s
  pretty (CatchProblem _) =
    "CatchProblem"

instance Show TCErr where
  show = PP.render

-- TCReport
------------------------------------------------------------------------

-- | A type useful to inspect what's going on.
data TCReport t p = TCReport
  { trSignature        :: !(Sig.Signature t)
  , trSolvedProblems   :: !(HS.HashSet ProblemIdInt)
  , trUnsolvedProblems :: !(Map.Map ProblemIdInt (Problem p))
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
typeError err = do
  mbD <- teDebug <$> ask
  case mbD of
    Nothing -> do
      return ()
    Just d -> do
      debug_ $
        "** About to throw error" $$
        "error:" //> err $$
        "stack trace:" //> PP.indent _ERROR_INDENT (PP.vcat (dStackTrace d))
  TC $ \(te, _) -> return $ Error $ DocErr (teCurrentSrcLoc te) err

assert :: (PP.Doc -> PP.Doc) -> TC t p s a -> TC t p s a
assert msg (TC m) = TC $ \(te, ts) -> do
  res <- m (te, ts)
  case res of
    Error (DocErr _ err)   -> error $ PP.render $ msg err
    Error (CatchProblem _) -> error "CatchProblem"
    OK ts' x               -> return $ OK ts' x

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
  sig <- tsSignature <$> get
  return $ f sig

withSignatureTermM :: (Sig.Signature t -> TermM a) -> TC t p s a
withSignatureTermM f = do
  sig <- tsSignature <$> get
  liftTermM $ f sig

getDefinition
  :: (IsTerm t) => Name -> TC t p s (Closed (Definition t))
getDefinition n = do
  sig <- tsSignature <$> get
  return $ Sig.getDefinition sig n

addDefinition
  :: (IsTerm t) => Name -> Closed (Definition t) -> TC t p s ()
addDefinition n def' =
  modify_ $ \ts -> ts{tsSignature = Sig.addDefinition (tsSignature ts) n def'}

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
    :: (IsTerm t) => Name -> Closed (Invertible t) -> TC t p s ()
addClauses f clauses = do
  def' <- getDefinition f
  let ext (Constant Postulate a) = return $ Function a clauses
      ext (Function _ _)         = error $ "TC.addClause: clause `" ++ show f ++ "' already added."
      ext (Constant k _)         = error $ "TC.addClause: constant `" ++ show k ++ "'"
      ext DataCon{}              = error $ "TC.addClause: constructor"
      ext Projection{}           = error $ "TC.addClause: projection"
  addDefinition f =<< ext def'

addMetaVar :: (IsTerm t) => Closed (Type t) -> TC t p s MetaVar
addMetaVar type_ = do
  loc <- teCurrentSrcLoc <$> ask
  sig <- tsSignature <$> get
  let (mv, sig') = Sig.addMetaVar sig loc type_
  let msg = do
        typeDoc <- prettyTermTC type_
        return $
          "*** addMetaVar" <+> PP.pretty mv $$
          typeDoc
  debug msg
  modify_ $ \ts -> ts{tsSignature = sig'}
  return mv

instantiateMetaVar
  :: (IsTerm t) => MetaVar -> Closed (Term t) -> TC t p s ()
instantiateMetaVar mv t = do
  let msg = do
        tDoc <- prettyTermTC t
        return $
          "*** instantiateMetaVar" <+> PP.pretty mv $$
          tDoc
  debug msg
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

_ERROR_INDENT :: Int
_ERROR_INDENT = 2

enableDebug :: TC t p s a -> TC t p s a
enableDebug (TC m) = TC $ \(te, ts) ->
  let te' = case teDebug te of
              Just _  -> te
              Nothing -> te{teDebug = Just initDebug}
  in m (te', ts)

disableDebug :: TC t p s a -> TC t p s a
disableDebug (TC m) = TC $ \(te, ts) -> m (te{teDebug = Nothing}, ts)

debugBracket :: TC t p s PP.Doc -> TC t p s a -> TC t p s a
debugBracket docM m = do
  doc <- assertDoc docM
  debug_ doc
  te <- ask
  let mbD = case teDebug te of
              Nothing -> Nothing
              Just d  -> Just d{dDepth = dDepth d + 1, dStackTrace = doc : dStackTrace d}
  local te{teDebug = mbD} m

debugBracket_ :: PP.Doc -> TC t p s a -> TC t p s a
debugBracket_ doc = debugBracket (return doc)

assertDoc :: TC t p s PP.Doc -> TC t p s PP.Doc
assertDoc = assert ("assertDoc: the doc action got an error:" <+>)

debug :: TC t p s PP.Doc -> TC t p s ()
debug docM = do
  mbD <- teDebug <$> ask
  case mbD of
    Nothing -> do
      return ()
    Just d -> do
      doc <- assertDoc docM
      TC $ \(_, ts) -> do
        let s  = PP.renderPretty 100 doc
        let pad = replicate (dDepth d * _ERROR_INDENT) ' '
        hPutStr stderr $ unlines $ map (pad ++) $ lines s
        return $ OK ts ()

debug_ :: PP.Doc -> TC t p s ()
debug_ doc = debug (return doc)

-- State
------------------------------------------------------------------------

getState :: TC t p s s
getState = tsState <$> get

putState :: s -> TC t p s ()
putState s = modify_ $ \ts -> ts{tsState = s}

-- Problem handling
------------------------------------------------------------------------

-- | An 'Int' version of the 'ProblemId', useful for debugging (see
-- 'TCReport').
type ProblemIdInt = Int

-- | A 'ProblemId' identifies a suspended computation and carries around
-- the type of the result of the computation it refers to.
newtype ProblemId a = ProblemId ProblemIdInt
  deriving (Show)

unProblemId :: ProblemId a -> ProblemIdInt
unProblemId (ProblemId pid) = pid

instance PP.Pretty (ProblemId a) where
  pretty (ProblemId pid) = PP.pretty pid

-- | To store problems, we store the context of the suspended
-- computation; and its state and description living in said context.
--
-- Both the type of the bound variable and the result type are
-- 'Typeable' since we store the solutions and problems dynamically so
-- that they can all be in the same 'Map.Map'.
data Problem p = forall a b. Problem
  { problemProblem    :: !(Maybe (p a b))
    -- ^ If 'Nothing', it means that we're just waiting on another
    -- problem to complete and we'll then return its result.
  , problemState      :: !ProblemState
  , problemSrcLoc     :: !SrcLoc
  , problemStackTrace :: !(Maybe [PP.Doc])
  }

type InterpretProblem t p s =
  forall a b. p a b -> a -> StuckTC t p s b

type DescribeProblem t p s =
  forall a b. p a b -> TC t p s PP.Doc

data WaitingOn
    = WOAnyMeta     !(HS.HashSet MetaVar)
    | WOAllProblems !(HS.HashSet ProblemIdInt)
    deriving (Show)

data ProblemState
    = WaitingOn      !WaitingOn
    | BoundToProblem !ProblemIdInt
    deriving (Show)

instance PP.Pretty ProblemState where
  pretty (WaitingOn (WOAnyMeta mvs))      = "WaitingOn metas" <+> PP.pretty (HS.toList mvs)
  pretty (WaitingOn (WOAllProblems pids)) = "WaitingOn problems" <+> PP.pretty (HS.toList pids)
  pretty (BoundToProblem pid)             = "BoundToProblem" <+> PP.pretty pid

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

stuckOn :: TC t p s (ProblemId a) -> StuckTC t p s a
stuckOn m = StuckOn <$> m

notStuck :: TC t p s a -> StuckTC t p s a
notStuck m = NotStuck <$> m

addProblem :: ProblemIdInt -> Problem p -> TC t p s (ProblemId a)
addProblem pid prob = do
  err <- tsCatchProblem <$> get
  if err
    then do
      mbD <- teDebug <$> ask
      case mbD of
        Nothing -> do
          return ()
        Just d -> do
          debug_ $
            "** About to throw error" $$
            "error: CatchProblem" $$
            "stack trace:" //> PP.indent _ERROR_INDENT (PP.vcat (dStackTrace d))
      TC $ \_ -> return $ Error $ CatchProblem $ case prob of
        Problem _ s _ _ -> s
    else modify $ \ts ->
           ( ts{tsUnsolvedProblems = Map.insert pid prob (tsUnsolvedProblems ts)}
           , ProblemId pid
           )

addFreshProblem :: Problem p -> TC t p s (ProblemId a)
addFreshProblem prob@(Problem mbProb _ _ _) = do
  pid <- modify $ \ts ->
         let count = tsProblemCount ts in (ts{tsProblemCount = count + 1}, count)
  debug $ do
    desc <- teDescribeProblem <$> ask
    probDoc <- case mbProb of
      Nothing -> return "Waiting to return."
      Just p  -> desc p
    return $
      "*** Adding new problem" <+> PP.pretty pid $$
      "state:" <+> PP.pretty (problemState prob) $$
      "description:" //> probDoc
  addProblem pid prob

-- | Store a new problem dependend on a set of 'MetaVar's.  When one of
-- them will be instantiated, the computation can be executed again.
newProblem
    :: WaitingOn
    -> p () b
    -> TC t p s (ProblemId b)
newProblem mvs m = do
    loc <- teCurrentSrcLoc <$> ask
    mbTrace <- fmap dStackTrace . teDebug <$> ask
    let prob = Problem{ problemProblem    = Just m
                      , problemState      = WaitingOn mvs
                      , problemSrcLoc     = loc
                      , problemStackTrace = mbTrace
                      }
    addFreshProblem prob

-- newProblem_
--     :: MetaVar
--     -> p () b
--     -> TC t p s (ProblemId b)
-- newProblem_ mv = newProblem (HS.singleton mv)

-- | @bindProblem pid desc (\x -> m)@ binds computation @m@ to problem
-- @pid@. When @pid@ is solved with result @t@, @m t@ will be executed.
bindProblem
    :: ProblemId a
    -> (p a b)
    -> TC t p s (ProblemId b)
bindProblem (ProblemId pid) f = do
    loc <- teCurrentSrcLoc <$> ask
    mbTrace <- fmap dStackTrace . teDebug <$> ask
    let prob = Problem{ problemProblem    = Just f
                      , problemState      = BoundToProblem pid
                      , problemSrcLoc     = loc
                      , problemStackTrace = mbTrace
                      }
    addFreshProblem prob

-- | This computation solves all problems that are solvable in the
-- current state.  Returns whether any problem was solved.
solveProblems :: forall p t s. TC t p s Bool
solveProblems = do
  debugBracket_ "*** solveProblems" $ do
    unsolvedProbs <- Map.toAscList . tsUnsolvedProblems <$> get
    -- Go over all unsolved problems and record if we made progress in any
    -- of them.
    progress <- fmap or $ forM unsolvedProbs $ \(pid, (Problem prob state loc mbTrace)) -> do
      -- Collect the state necessary to execute the current problem, if
      -- available.
      mbSolution :: Maybe ProblemSolution <- case state of
        -- If we're waiting on metavars, check if at least one is
        -- instantiated.  The state will be ().
        WaitingOn (WOAnyMeta mvs) -> do
          withSignature $ \sig -> msum
            [ problemSolution () <$ HMS.lookup mv (Sig.metaVarsBodies sig)
            | mv <- HS.toList mvs
            ]
        WaitingOn (WOAllProblems pids) -> do
          unsolvedProbsMap <- tsUnsolvedProblems <$> get
          return $ if all (`Map.member` unsolvedProbsMap) $ HS.toList pids
            then Just (problemSolution ())
            else Nothing
        -- If we're bound to another problem, retrieve its result if
        -- available.
        BoundToProblem boundTo ->
          HMS.lookup boundTo . tsSolvedProblems <$> get
      case mbSolution of
        Nothing       -> return False
        Just solution -> True <$ solveProblem pid prob loc mbTrace solution
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
      -> Maybe [PP.Doc]
      -- ^ ...and a stacktrace, if we have it.
      -> ProblemSolution
      -- ^ Solution to the problem we were waiting on.
      -> TC t p s ()
    solveProblem pid mbP loc mbTrace (ProblemSolution x) = do
      -- Delete the problem from the list of unsolved problems.
      modify_ $ \ts -> ts{tsUnsolvedProblems = Map.delete pid (tsUnsolvedProblems ts)}
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
          te <- ask
          let comp = teInterpretProblem te
          let te' = case (teDebug te, mbTrace) of
                      (Nothing, _)          -> te
                      (_,      Nothing)     -> te
                      (Just d, Just trace_) -> te{teDebug = Just d{dStackTrace = trace_}}
          local te' $ atSrcLoc loc $ do
            debug_ ("** Resuming problem" <+> PP.pretty pid)
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
            Problem (Nothing :: Maybe (p a b)) (BoundToProblem boundTo) loc mbTrace
          return ()

solveProblems_ :: TC t p s ()
solveProblems_ = void solveProblems

catchProblem :: TC t p s a -> TC t p s (Either ProblemState a)
catchProblem m = debugBracket_ "*** catchProblem" $ TC $ \(te, ts) -> do
  res <- unTC m (te, ts{tsCatchProblem = True})
  case res of
    Error (CatchProblem pid) -> return $ OK ts $ Left pid
    Error err                -> return $ Error err
    OK ts' x                 -> return $ OK ts'{tsCatchProblem = tsCatchProblem ts} $ Right x

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
      StuckOn <$> bindProblem pid p

-- Freezing
------------------------------------------------------------------------

freeze :: TC t p s a -> TC t p s a
freeze m = do
  te <- ask
  local te{teFrozen = True} m

-- Utils
------------------------------------------------------------------------

modify :: (TCState t p s -> (TCState t p s, a)) -> TC t p s a
modify f = TC $ \(te, ts) ->
  if teFrozen te
  then unTC (typeError "Trying to modify state when frozen.") (te, ts)
  else let (ts', x) = f ts in return $ OK ts' x

modify_ :: (TCState t p s -> TCState t p s) -> TC t p s ()
modify_ f = modify $ \ts -> (f ts, ())

get :: TC t p s (TCState t p s)
get = TC $ \(_, ts) -> return $ OK ts ts

ask :: TC t p s (TCEnv t p s)
ask = TC $ \(te, ts) -> return $ OK ts te

local :: TCEnv t p s -> TC t p s a -> TC t p s a
local te (TC m) = TC $ \(_, ts) -> m (te, ts)

prettyTermTC :: (IsTerm t) => t -> TC t p s PP.Doc
prettyTermTC t = withSignatureTermM $ \sig -> prettyTerm sig t
