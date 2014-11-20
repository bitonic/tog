{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE NoImplicitPrelude #-}
module TypeCheck3.Monad
  ( -- * Monad definition
    TC
  , TCState(..)
  , tcState
  , TCErr(..)
  , initTCState
  , runTC
  , catchTC
    -- * Operations
    -- ** Errors
  , typeError
  , assert
  , assert_
    -- ** Source location
  , atSrcLoc
    -- ** Definition handling
  , addDefinition
  , getDefinition
  , addConstant
  , addDataCon
  , addProjection
  , addClauses
    -- ** MetaVar handling
  , addMetaVar
  , uncheckedInstantiateMetaVar
  , getMetaVarType
  , getMetaVarBody
  , unsafeRemoveMetaVar
    -- ** State handling
  , mapTC
  , nestTC
  ) where

import qualified Control.Lens                     as L
import qualified Control.Monad.State.Class        as State

import           Prelude.Extended                 hiding (any)
import           Instrumentation
import           PrettyPrint                      ((<+>), ($$), (//>))
import qualified PrettyPrint                      as PP
import           Syntax
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
newtype TC t s a = TC
  {unTC :: (TCEnv, TCState t s) -> IO (TCState t s, Either TCErr a)}
  deriving (Functor)

instance Applicative (TC t s) where
  pure  = return
  (<*>) = ap

instance Monad (TC t s) where
  return x = TC $ \(_, ts) -> return (ts, Right x)

  TC m >>= f =
    TC $ \s@(te, _) -> do
      (ts, mbX) <- m s
      case mbX of
        Right x -> unTC (f x) (te, ts)
        Left e  -> return (ts, Left e)

instance MonadIO (TC t s) where
  liftIO m = TC $ \(_, ts) -> (ts,) . Right <$> m

instance MonadTerm t (TC t s) where
  askSignature = tsSignature <$> get

catchTC
  :: TC t s a -> TC t s (Either PP.Doc a)
catchTC m = TC $ \(te, ts) -> do
  (ts', mbErr) <- unTC m (te, ts)
  return $ case mbErr of
    Left e  -> (ts', Right (Left (PP.pretty e)))
    Right x -> (ts', Right (Right x))

-- | Takes a 'TCState' and a computation on a closed context and
-- produces an error or a result with a new state.
runTC :: (IsTerm t)
      => TCState t s -> TC t s a -> IO (Either PP.Doc a, TCState t s)
runTC ts (TC m) = do
  mbErr <- m (initEnv, ts)
  return $ case mbErr of
    (ts', Left e)  -> (Left (PP.pretty e), ts')
    (ts', Right x) -> (Right x, ts')

data TCEnv = TCEnv
    { teCurrentSrcLoc  :: !SrcLoc
    }

initEnv :: TCEnv
initEnv =
  TCEnv{ teCurrentSrcLoc = noSrcLoc
       }

data TCState t s = TCState
    { tsSignature        :: !(Sig.Signature t)
    , tsState            :: !s
    } deriving (Functor)

-- | An empty state.
initTCState
  :: s -> TCState t s
initTCState s = TCState
  { tsSignature        = Sig.empty
  , tsState            = s
  }

tcState :: TCState t s -> s
tcState = tsState

data TCErr
    = DocErr SrcLoc PP.Doc
    deriving (Typeable)

instance PP.Pretty TCErr where
  pretty (DocErr p s) =
    "Error at" <+> PP.pretty p <+> ":" $$
    PP.nest 2 s

instance Show TCErr where
  show = PP.render

-- Errors
------------------------------------------------------------------------

-- | Fail with an error message.
typeError :: PP.Doc -> TC t s b
typeError err = do
  stackTrace "typeError" err
  TC $ \(te, ts) -> return (ts, Left (DocErr (teCurrentSrcLoc te) err))

assert :: (PP.Doc -> TC t s PP.Doc) -> TC t s a -> TC t s a
assert msg m = do
  mbErr <- catchTC m
  case mbErr of
    Left err -> fatalError . PP.render =<< msg err
    Right x  -> return x

assert_ :: (PP.Doc -> PP.Doc) -> TC t s a -> TC t s a
assert_ msg = assert (return . msg)

-- SrcLoc
------------------------------------------------------------------------

-- | Run some action with the given 'SrcLoc'.
atSrcLoc :: HasSrcLoc a => a -> TC t s b -> TC t s b
atSrcLoc x (TC m) = TC $ \(te, ts) -> m (te{teCurrentSrcLoc = srcLoc x}, ts)

-- Signature
------------------------------------------------------------------------

getDefinition
  :: (IsTerm t) => Name -> TC t s (Closed (Definition t))
getDefinition n = do
  sig <- tsSignature <$> get
  Just def' <- return $ Sig.getDefinition sig n
  return def'

addDefinition
  :: (IsTerm t) => Name -> Closed (Definition t) -> TC t s ()
addDefinition n def' =
  modify_ $ \ts -> ts{tsSignature = Sig.addDefinition (tsSignature ts) n def'}

addConstant
    :: (IsTerm t)
    => Name -> Closed (Type t) -> Constant t -> TC t s ()
addConstant x a k = addDefinition x (Constant a k)

addDataCon
    :: (IsTerm t)
    => Name -> Name -> Natural -> Tel.Tel (Type t) -> Type t -> TC t s ()
addDataCon c d args tel t = addDefinition c (DataCon d args tel t)

addProjection
    :: (IsTerm t)
    => Projection -> Name -> Tel.Tel (Type t) -> Type t -> TC t s ()
addProjection p r tel t = addDefinition (pName p) (Projection (pField p) r tel t)

addClauses
    :: (IsTerm t) => Name -> Closed (Invertible t) -> TC t s ()
addClauses f clauses = do
  def' <- getDefinition f
  let ext (Constant a (Function Nothing)) =
        return $ Constant a (Function (Just clauses))
      ext (Constant _ (Function (Just _))) =
        fatalError $ "TC.addClauses: clause `" ++ show f ++ "' already added."
      ext (Constant _ _) =
        fatalError "TC.addClauses: bad constant"
      ext DataCon{} =
        fatalError $ "TC.addClauses: constructor"
      ext Projection{} =
        fatalError $ "TC.addClauses: projection"
  addDefinition f =<< ext def'

addMetaVar :: (IsTerm t) => Closed (Type t) -> TC t s MetaVar
addMetaVar type_ = do
  loc <- teCurrentSrcLoc <$> ask
  sig <- tsSignature <$> get
  let (mv, sig') = Sig.addMetaVar sig loc type_
  debug "addMetaVar" $ do
    typeDoc <- prettyM type_
    return $
      "metavar" <+> PP.pretty mv $$
      "type" //> typeDoc
  modify_ $ \ts -> ts{tsSignature = sig'}
  return mv

uncheckedInstantiateMetaVar
  :: (IsTerm t)
  => MetaVar -> MetaVarBody t -> TC t s ()
uncheckedInstantiateMetaVar mv t = do
  modify_ $ \ts -> ts{tsSignature = Sig.instantiateMetaVar (tsSignature ts) mv t}

getMetaVarType
  :: (IsTerm t) => MetaVar -> TC t s (Closed (Type t))
getMetaVarType mv = do
  sig <- tsSignature <$> get
  return $ Sig.getMetaVarType sig mv

getMetaVarBody
  :: (IsTerm t) => MetaVar -> TC t s (Maybe (MetaVarBody t))
getMetaVarBody mv = do
  sig <- tsSignature <$> get
  return $ Sig.getMetaVarBody sig mv

unsafeRemoveMetaVar
  :: (IsTerm t) => MetaVar -> TC t s ()
unsafeRemoveMetaVar mv = do
  debug_ "unsafeRemoveMeta" (PP.pretty mv)
  modify_ $ \ts -> ts{tsSignature = Sig.unsafeRemoveMetaVar (tsSignature ts) mv}

-- State
------------------------------------------------------------------------

instance State.MonadState s (TC t s) where
  get = tsState <$> get
  put s = modify_ $ \ts -> ts{tsState = s}
  state f = modify $ \ts -> let (x, s) = f (tsState ts) in (ts{tsState = s}, x)

mapTC :: L.Lens' s s' -> TC t s' a -> TC t s a
mapTC l (TC m) = TC $ \(te, ts) -> do
  (ts'', x) <- m (te, L.view l <$> ts)
  return ((\s -> L.set l s (tsState ts)) <$> ts'', x)

-- | Runs an action with a different state, but with the same
-- environment and signature.
nestTC :: s' -> TC t s' a -> TC t s (a, s')
nestTC s (TC m) = TC $ \(te, ts) -> do
  (ts', mbX) <- m (te, s <$ ts)
  let ts'' = tsState ts <$ ts'
  return $ case mbX of
    Left e  -> (ts'', Left e)
    Right x -> (ts'', Right (x, tsState ts'))

-- Utils
------------------------------------------------------------------------

modify :: (TCState t s -> (TCState t s, a)) -> TC t s a
modify f = TC $ \(_, ts) ->
  let (ts', x) = f ts in return (ts', Right x)

modify_ :: (TCState t s -> TCState t s) -> TC t s ()
modify_ f = modify $ \ts -> (f ts, ())

get :: TC t s (TCState t s)
get = TC $ \(_, ts) -> return (ts, Right ts)

ask :: TC t s (TCEnv)
ask = TC $ \(te, ts) -> return (ts, Right te)
