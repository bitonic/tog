{-# LANGUAGE OverloadedStrings #-}
module TypeCheck3.Monad
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
  , fatalError
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
    -- ** State handling
  , mapTC
    -- * Debugging
  , debugBracket
  , debugBracket_
  , debug
  , debug_
  ) where

import           Control.Exception.Base           (throwIO, catch, try, Exception)
import qualified Control.Lens                     as L
import qualified Control.Monad.State.Class        as State
import           System.IO                        (hPutStr, stderr)

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
newtype TC t s a = TC {unTC :: (TCEnv, TCState t s) -> IO (TCState t s, a)}
  deriving (Functor)

instance Applicative (TC t s) where
  pure  = return
  (<*>) = ap

instance Monad (TC t s) where
  return x = TC $ \(_, ts) -> return (ts, x)

  TC m >>= f =
    TC $ \s@(te, _) -> do
      (ts, x) <- m s
      unTC (f x) (te, ts)

catchTC
  :: TC t s a -> TC t s (Either PP.Doc a)
catchTC m = TC $ \(te, ts) -> do
  mbErr <- try $ unTC m (te, ts)
  case mbErr of
    Left (e :: TCErr) -> return (ts, Left (PP.pretty e))
    Right (ts', x)    -> return (ts', Right x)

-- | Takes a 'TCState' and a computation on a closed context and
-- produces an error or a result with a new state.
runTC :: (IsTerm t)
      => Bool -> TCState t s
      -> TC t s a -> IO (Either PP.Doc (a, TCState t s))
runTC debug ts (TC m) = do
  mbErr <- try $ m (initEnv{teDebug = if debug then Just initDebug else Nothing}, ts)
  return $ case mbErr of
    Left (e :: TCErr) -> Left $ PP.pretty e
    Right (ts', x)    -> Right (x, ts')

data TCEnv = TCEnv
    { teCurrentSrcLoc    :: !SrcLoc
    , teDebug            :: !(Maybe Debug)
    }

data Debug = Debug
  { dDepth      :: !Int
  , dStackTrace :: ![PP.Doc]
  }

initDebug :: Debug
initDebug = Debug 0 []

initEnv :: TCEnv
initEnv =
  TCEnv{ teCurrentSrcLoc    = noSrcLoc
       , teDebug            = Nothing
       }

data TCState t s = TCState
    { tsSignature        :: !(Sig.Signature t)
    , tsState            :: !s
    }
    deriving (Functor)

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
    "Error at" <+> PP.text (show p) <+> ":" $$
    PP.nest 2 s

instance Show TCErr where
  show = PP.render

instance Exception TCErr

-- TCReport
------------------------------------------------------------------------

-- | A type useful to inspect what's going on.
data TCReport t p = TCReport
  { trSignature        :: !(Sig.Signature t)
  }

tcReport :: (IsTerm t) => TCState t s -> TCReport t p
tcReport ts = TCReport
  { trSignature        = sig
  }
  where
    sig = tsSignature ts

-- Errors
------------------------------------------------------------------------

-- | Fail with an error message.
typeError :: PP.Doc -> TC t s b
typeError err = do
  mbDebug <- teDebug <$> ask
  forM_ mbDebug $ \d ->
    debug_ $
      "** About to throw error" $$
      "error:" //> err $$
      "stack trace:" //> PP.indent _ERROR_INDENT (PP.vcat (dStackTrace d))
  TC $ \(te, _) -> throwIO $ DocErr (teCurrentSrcLoc te) err

fatalError :: String -> TC t s b
fatalError s = do
  mbDebug <- teDebug <$> ask
  forM_ mbDebug $ \d ->
    debug_ $
      "** SHUTTING DOWN" $$
      "error:" //> PP.text s $$
      "stack trace:" //> PP.indent _ERROR_INDENT (PP.vcat (dStackTrace d))
  error s

assert :: (PP.Doc -> PP.Doc) -> TC t s a -> TC t s a
assert msg m = do
  mbErr <- catchTC m
  case mbErr of
    Left err -> fatalError $ PP.render $ msg err
    Right x  -> return x

-- SrcLoc
------------------------------------------------------------------------

-- | Run some action with the given 'SrcLoc'.
atSrcLoc :: HasSrcLoc a => a -> TC t s b -> TC t s b
atSrcLoc x (TC m) = TC $ \(te, ts) -> m (te{teCurrentSrcLoc = srcLoc x}, ts)

-- TermM
------------------------------------------------------------------------

liftTermM :: TermM a -> TC t s a
liftTermM m = TC $ \(_, ts) -> do
  x <- m
  return $ (ts, x)

-- Signature
------------------------------------------------------------------------

-- | Do something with the current signature.
withSignature :: (Sig.Signature t -> a) -> TC t s a
withSignature f = do
  sig <- tsSignature <$> get
  return $ f sig

withSignatureTermM :: (Sig.Signature t -> TermM a) -> TC t s a
withSignatureTermM f = do
  sig <- tsSignature <$> get
  liftTermM $ f sig

getDefinition
  :: (IsTerm t) => Name -> TC t s (Closed (Definition t))
getDefinition n = do
  sig <- tsSignature <$> get
  return $ Sig.getDefinition sig n

addDefinition
  :: (IsTerm t) => Name -> Closed (Definition t) -> TC t s ()
addDefinition n def' =
  modify_ $ \ts -> ts{tsSignature = Sig.addDefinition (tsSignature ts) n def'}

addConstant
    :: (IsTerm t)
    => Name -> ConstantKind -> Closed (Type t) -> TC t s ()
addConstant x k a = addDefinition x (Constant k a)

addDataCon
    :: (IsTerm t)
    => Name -> Name -> Tel.Tel (Type t) -> Type t -> TC t s ()
addDataCon c d tel t = addDefinition c (DataCon d tel t)

addProjection
    :: (IsTerm t)
    => Name -> Field -> Name -> Tel.Tel (Type t) -> Type t -> TC t s ()
addProjection f n r tel t = addDefinition f (Projection n r tel t)

addClauses
    :: (IsTerm t) => Name -> Closed (Invertible t) -> TC t s ()
addClauses f clauses = do
  def' <- getDefinition f
  let ext (Constant Postulate a) = return $ Function a clauses
      ext (Function _ _)         = fatalError $ "TC.addClause: clause `" ++ show f ++ "' already added."
      ext (Constant k _)         = fatalError $ "TC.addClause: constant `" ++ show k ++ "'"
      ext DataCon{}              = fatalError $ "TC.addClause: constructor"
      ext Projection{}           = fatalError $ "TC.addClause: projection"
  addDefinition f =<< ext def'

addMetaVar :: (IsTerm t) => Closed (Type t) -> TC t s MetaVar
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
  :: (IsTerm t) => MetaVar -> Closed (Term t) -> TC t s ()
instantiateMetaVar mv t = do
  let msg = do
        tDoc <- prettyTermTC t
        return $
          "*** instantiateMetaVar" <+> PP.pretty mv $$
          tDoc
  debug msg
  modify_ $ \ts -> ts{tsSignature = Sig.instantiateMetaVar (tsSignature ts) mv t}

getMetaVarType
  :: (IsTerm t) => MetaVar -> TC t s (Closed (Type t))
getMetaVarType mv = do
  sig <- tsSignature <$> get
  return $ Sig.getMetaVarType sig mv

getMetaVarBody
  :: (IsTerm t) => MetaVar -> TC t s (Maybe (Closed (Term t)))
getMetaVarBody mv = do
  sig <- tsSignature <$> get
  return $ Sig.getMetaVarBody sig mv

-- Debugging
------------------------------------------------------------------------

_ERROR_INDENT :: Int
_ERROR_INDENT = 2

debugBracket :: TC t s PP.Doc -> TC t s a -> TC t s a
debugBracket docM m = do
  doc <- assertDoc docM
  debug_ doc
  te <- ask
  let mbD = case teDebug te of
              Nothing -> Nothing
              Just d  -> Just d{dDepth = dDepth d + 1, dStackTrace = doc : dStackTrace d}
  local te{teDebug = mbD} m

debugBracket_ :: PP.Doc -> TC t s a -> TC t s a
debugBracket_ doc = debugBracket (return doc)

assertDoc :: TC t s PP.Doc -> TC t s PP.Doc
assertDoc = assert ("assertDoc: the doc action got an error:" <+>)

debug :: TC t s PP.Doc -> TC t s ()
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
        return (ts, ())

debug_ :: PP.Doc -> TC t s ()
debug_ doc = debug (return doc)

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

-- Utils
------------------------------------------------------------------------

modify :: (TCState t s -> (TCState t s, a)) -> TC t s a
modify f = TC $ \(_, ts) ->
  let (ts', x) = f ts in return (ts', x)

modify_ :: (TCState t s -> TCState t s) -> TC t s ()
modify_ f = modify $ \ts -> (f ts, ())

get :: TC t s (TCState t s)
get = TC $ \(_, ts) -> return (ts, ts)

ask :: TC t s (TCEnv)
ask = TC $ \(te, ts) -> return (ts, te)

local :: TCEnv -> TC t s a -> TC t s a
local te (TC m) = TC $ \(_, ts) -> m (te, ts)

prettyTermTC :: (IsTerm t) => t -> TC t s PP.Doc
prettyTermTC t = withSignatureTermM $ \sig -> prettyTerm sig t
