{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE UndecidableInstances #-}
module Term.Types
  ( -- * Var
    Var
  , unVar
  , mkVar
  , varIndex
  , varName
  , boundVar
  , weakenVar
  , weakenVar_
  , strengthenVar
  , strengthenVar_
    -- * Named
  , named
  , Named(..)
    -- * Terms
  , TermView(..)
  , Projection(..)
  , Head(..)
  , Opened(..)
  , Elim(..)
  , isApply
  , isProj
  , Field(..)
    -- * Term typeclasses
    -- ** Metas
  , MetaSet
  , Metas(..)
  , Meta(..)
    -- ** Nf
  , Nf(..)
    -- ** Pretty
  , PrettyM(..)
    -- ** Subst
  , ApplySubstM
  , runApplySubst
  , ApplySubst(..)
  , applySubst
    -- ** SynEq
  , SynEq(..)
    -- * IsTerm
  , IsTerm(..)
  , whnfView
    -- ** Blocked
  , Blocked(..)
  , BlockedHead(..)
  , isBlocked
  , ignoreBlocking
    -- ** Utilities
  , var
  , lam
  , pi
  , equal
  , app
  , def
  , meta
  , con
    -- * Definition
  , Contextual(..)
  , openContextual
  , ignoreContextual
  , Module
  , Definition(..)
  , openDefinition
  , Constant(..)
  , FunInst(..)
  , ClauseBody
  , Clause(..)
  , Pattern(..)
  , patternBindings
  , patternsBindings
  , Invertible(..)
  , TermHead(..)
  , ignoreInvertible
  , definitionType
    -- * MonadTerm
  , MonadTerm(..)
  , TermM
  , runTermM
  , getDefinition
  , getMetaType
  , lookupMetaBody
    -- * Signature
  , MetaBody(..)
  , metaBodyToTerm
  , Signature(..)
  , sigEmpty
    -- ** Querying
  , sigGetDefinition
  , sigLookupDefinition
  , sigGetMetaType
  , sigLookupMetaBody
  , sigDefinedNames
  , sigDefinedMetas
    -- ** Updating
  , sigAddPostulate
  , sigAddData
  , sigAddRecordCon
  , sigAddTypeSig
  , sigAddClauses
  , sigAddProjection
  , sigAddDataCon
  , sigAddModule
  , sigAddMeta
  , sigInstantiateMeta
  --   -- ** Utils
  -- , sigToScope
    -- * Context
  , Ctx(..)
  , ctxSingleton
  , ctxLength
  , ctxWeaken
  , ctxWeaken_
  , ctxLookupName
  , ctxLookupVar
  , ctxGetVar
  , ctxVars
  , ctxPi
  , ctxLam
  , ctxApp
    -- * Telescope
  , Tel(..)
  , ctxToTel
  , telToCtx
  , telLength
  , telAppend
  , telDischarge
  , telPi
  , telVars
  , telApp
    -- * Substitution
  , Subst
    -- ** Smart constructors
  , subId
  , subSingleton
  , subWeaken
  , subInstantiate
  , subStrengthen
  , subLift
    -- ** Operations
  , subChain
  , subCompose
  , subLookup
  , subNull
    -- ** Operations on terms
  , weaken
  , weaken_
  , strengthen
  , strengthen_
  , instantiate
  , instantiate_
  , safeStrengthen
  , getAbsName
  , getAbsName_
  , eliminate
    -- * Clauses invertibility
  , termHead
  , checkInvertibility
  ) where

import           Control.Monad.Trans.Reader       (ReaderT, runReaderT, ask)
import qualified Data.HashSet                     as HS
import qualified Data.HashMap.Strict              as HMS

import           Instrumentation
import           TogPrelude
import           Names
import qualified PrettyPrint                      as PP
import           PrettyPrint                      ((<+>), ($$), (//>))
import           Term.Subst
import           Term.Synonyms

#include "impossible.h"

-- Var
------------------------------------------------------------------------

newtype Var = V (Named Natural)
  deriving (Show, Read, Eq, Ord, Hashable)

unVar :: Var -> Named Natural
unVar (V v) = v

mkVar :: Name -> Natural -> Var
mkVar _ i | i < 0 = error "impossible.mkVar"
mkVar n i = V $ named n i

varIndex :: Var -> Natural
varIndex = unNamed . unVar

varName :: Var -> Name
varName = namedName . unVar

instance PP.Pretty Var where
  pretty v = PP.pretty (varIndex v) <> "#" <> PP.pretty (varName v)

boundVar :: Name -> Var
boundVar n = V $ named n 0

weakenVar :: Natural -> Natural -> Var -> Var
weakenVar from by (V (Named n ix)) =
  let ix' = if ix >= from
            then ix + by
            else ix
  in V $ Named n ix'

weakenVar_ :: Natural -> Var -> Var
weakenVar_ = weakenVar 0

strengthenVar :: Natural -> Natural -> Var -> Maybe Var
strengthenVar from by (V (Named n ix)) =
  let ix' | ix < from      = Just ix
          | ix < from + by = Nothing
          | otherwise      = Just $ ix - by
  in V . Named n <$> ix'

strengthenVar_ :: Natural -> Var -> Maybe Var
strengthenVar_ = strengthenVar 0

-- Named
------------------------------------------------------------------------

named :: Name -> a -> Named a
named = Named

data Named a = Named
  { namedName :: !Name
  , unNamed   :: !a
  } deriving (Show, Read, Functor, Foldable, Traversable, Generic)

instance Eq a => Eq (Named a) where
  Named _ v1 == Named _ v2 = v1 == v2

instance Ord a => Ord (Named a) where
  Named _ v1 `compare` Named _ v2 = v1 `compare` v2

instance (Hashable a) => Hashable (Named a)

-- Record 'Field's
------------------------------------------------------------------------

-- | The field of a projection.
newtype Field = Field {unField :: Natural}
    deriving (Eq, Ord, Show, Read, Hashable)

-- Terms
------------------------------------------------------------------------

-- | A 'Head' heads a neutral term -- something which can't reduce
-- further.
data Head t
    = Var !Var
    | Def !(Opened QName t)
    | Meta !Meta
    | J
    deriving (Show, Read, Eq, Generic, Functor)

instance (Hashable t) => Hashable (Head t)

data Opened key t = Opened
  { opndKey  :: !key
  , opndArgs :: ![Term t]
    -- ^ The arguments of the contexts the definition corresponding to
    -- 'DefKey' is in.  They must match the length of the telescope in
    -- 'Contextual'.
  } deriving (Show, Read, Eq, Generic, Functor, Foldable, Traversable)

instance (Hashable key, Hashable t) => Hashable (Opened key t)

instance Bifunctor Opened where
  bimap f g (Opened k args) = Opened (f k) (fmap g args)

-- | 'Elim's are applied to 'Head's.  They're either arguments applied
-- to functions, or projections applied to records.
data Elim t
  = Apply !t
  | Proj !(Opened Projection t)
  deriving (Eq, Show, Read, Generic, Functor, Foldable, Traversable)

instance (Hashable t) => Hashable (Elim t)

isApply :: Elim (Term t) -> Maybe (Term t)
isApply (Apply v) = Just v
isApply Proj{}    = Nothing

isProj :: Elim (Term t) -> Maybe (Opened Projection t)
isProj Apply{}  = Nothing
isProj (Proj p) = Just p

data Projection = Projection'
  { pName  :: !QName
  , pField :: !Field
  } deriving (Show, Read, Eq, Ord, Generic)

instance Hashable Projection

instance PP.Pretty Projection where
  pretty = PP.pretty . pName

-- | The 'TermView' lets us pattern match on terms.  The actual
-- implementation of terms might be different, but we must be able to
-- get a 'TermView' out of it.  See 'View'.
data TermView t
    = Pi !(Type t) !(Abs (Type t))
    | Lam !(Abs t)
    | Equal !(Type t) !(Term t) !(Term t)
    | Refl
    | Set
    | Con !(Opened QName t) [Term t]
    | App !(Head t) [Elim t]
    deriving (Eq, Generic, Show)

instance (Hashable t) => Hashable (TermView t)

-- Term typeclasses
------------------------------------------------------------------------

-- Metas
-----------

type MetaSet = HS.HashSet Meta

class Metas t a where
  metas :: (MonadTerm t m) => a -> m MetaSet

instance Metas t (Elim t) where
  metas (Apply t) = metas t
  metas (Proj _)  = return mempty

instance Metas t a => Metas t [a] where
  metas xs = mconcat <$> mapM metas xs

-- Nf
------------------------------------------------------------------------

class Nf t a where
  nf :: (MonadTerm t m) => a -> m a

instance Nf t (Elim t) where
  nf (Proj p)  = return $ Proj p
  nf (Apply t) = Apply <$> nf t

instance Nf t a => Nf t [a] where
  nf = mapM nf

-- Pretty
------------------------------------------------------------------------

class PrettyM t a where
  {-# MINIMAL prettyPrecM | prettyM #-}

  prettyPrecM :: (MonadTerm t m) => Int -> a -> m PP.Doc
  prettyPrecM _ = prettyM

  prettyM :: (MonadTerm t m) => a -> m PP.Doc
  prettyM = prettyPrecM 0

instance PrettyM t (Elim t) where
  prettyPrecM p (Apply t) = do
    tDoc <- prettyPrecM p t
    return $ PP.condParens (p > 0) $ "$" <+> tDoc
  prettyPrecM _ (Proj (Opened p args)) = do
    -- Hacky
    t <- def (Opened (pName p) args) []
    tDoc <- prettyM t
    let pDoc = if null args then tDoc else PP.parens tDoc
    return $ "." <> pDoc

instance PrettyM t a => PrettyM t [a] where
  prettyM x = PP.list <$> mapM prettyM x

instance (PP.Pretty key) => PrettyM t (Opened key t) where
  prettyM (Opened key args) = do
    argsDoc <- prettyM args
    return $
      "Opened" $$
      "key:" <+> PP.pretty key $$
      "args:" //> argsDoc

instance PrettyM t Var where
  prettyM = return . PP.pretty

-- Subst
------------------------------------------------------------------------

type ApplySubstM = ExceptT Name

runApplySubst :: ApplySubstM m a -> m (Either Name a)
runApplySubst = runExceptT

class ApplySubst t a where
  safeApplySubst :: (MonadTerm t m) => a -> Subst t -> ApplySubstM m a

instance ApplySubst t (Elim t) where
  safeApplySubst (Proj p)  _   = return $ Proj p
  safeApplySubst (Apply t) sub = Apply <$> safeApplySubst t sub

instance ApplySubst t a => ApplySubst t [a] where
  safeApplySubst t rho = mapM (`safeApplySubst` rho) t

instance ApplySubst t (Clause t) where
  safeApplySubst (Clause pats t) rho =
    Clause pats <$> safeApplySubst t (subLift (patternsBindings pats) rho)

instance ApplySubst t (Definition Const t) where
  safeApplySubst (Constant type_ constant) rho =
    Constant <$> safeApplySubst type_ rho <*> safeApplySubst constant rho
  safeApplySubst (DataCon tyCon args dataConType) rho =
    DataCon tyCon args <$> safeApplySubst dataConType rho
  safeApplySubst (Projection fld tyCon projType) rho =
    Projection fld tyCon <$> safeApplySubst projType rho
  safeApplySubst (Module (Contextual tel names)) rho =
    Module <$> (Contextual <$> safeApplySubst tel rho <*> pure names)

instance ApplySubst t (Constant Const t) where
  safeApplySubst Postulate _ = do
    return Postulate
  safeApplySubst (Data dataCons) _ = do
    return $ Data dataCons
  safeApplySubst (Record dataCon projs) _ = do
    return $ Record dataCon projs
  safeApplySubst (Function inst) rho = do
    Function <$> safeApplySubst inst rho

instance ApplySubst t (FunInst t) where
  safeApplySubst Open       _   = return Open
  safeApplySubst (Inst inv) rho = Inst <$> safeApplySubst inv rho

instance ApplySubst t (Invertible t) where
  safeApplySubst (NotInvertible clauses) rho = do
    NotInvertible <$> safeApplySubst clauses rho
  safeApplySubst (Invertible clauses) rho = do
    clauses' <- forM clauses $ \(th, clause) -> do
      (th,) <$> safeApplySubst clause rho
    return $ Invertible clauses'

instance (ApplySubst t a) => ApplySubst t (Contextual t a) where
  safeApplySubst (Contextual tel x) rho =
    Contextual <$> safeApplySubst tel rho
               <*> safeApplySubst x (subLift (telLength tel) rho)

instance (ApplySubst t a) => ApplySubst t (Opened key a) where
  safeApplySubst (Opened n args) rho = Opened n <$> safeApplySubst args rho

applySubst :: (MonadTerm t m, ApplySubst t a) => a -> Subst t -> m a
applySubst x rho = do
  nameOrRes <- runExceptT $ safeApplySubst x rho
  case nameOrRes of
    Left name -> error $ "applySubst: couldn't strengthen because of " ++ show name
    Right res -> return res

-- SynEq
------------------------------------------------------------------------

class SynEq t a where
  synEq :: (MonadTerm t m) => a -> a -> m Bool

instance SynEq t (Elim t) where
  synEq e1 e2 = case (e1, e2) of
    (Proj p1,  Proj p2)  -> synEq p1 p2
    (Apply t1, Apply t2) -> synEq t1 t2
    (_,        _)        -> return False

instance SynEq t (Blocked t) where
  synEq blockedX blockedY = case (blockedX, blockedY) of
    (NotBlocked x, NotBlocked y) ->
      synEq x y
    (BlockingHead mv1 els1, BlockingHead mv2 els2) | mv1 == mv2 ->
      synEq els1 els2
    (BlockedOn mvs1 f1 els1, BlockedOn mvs2 f2 els2) | mvs1 == mvs2 ->
      synEq (f1, els1) (f2, els2)
    (_, _) ->
      return False

instance SynEq t a => SynEq t [a] where
  synEq []       []       = return True
  synEq (x : xs) (y : ys) = synEq (x, xs) (y, ys)
  synEq _        _        = return False

instance (SynEq t a, SynEq t b) => SynEq t (a, b) where
  synEq (x1, y1) (x2, y2) = do
    b <- synEq x1 x2
    if b then synEq y1 y2 else return False

instance (SynEq t a, SynEq t b, SynEq t c) => SynEq t (a, b, c) where
  synEq (x1, y1, z1) (x2, y2, z2) = do
    b1 <- synEq x1 x2
    if b1
      then do
        b2 <- synEq y1 y2
        if b2 then synEq z1 z2 else return False
      else return False

instance (Eq key) => SynEq t (Opened key t) where
  synEq (Opened k1 args1) (Opened k2 args2) =
    if k1 == k2
      then synEq args1 args2
      else return False

instance SynEq t (BlockedHead t) where
  synEq (BlockedOnFunction f1) (BlockedOnFunction f2) =
    synEq f1 f2
  synEq BlockedOnJ BlockedOnJ =
    return True
  synEq _ _ =
    return False

instance SynEq t (Head t) where
  synEq (Var v1) (Var v2) =
    return $ v1 == v2
  synEq (Def dk1) (Def dk2) =
    synEq dk1 dk2
  synEq J J =
    return True
  synEq (Meta mv1) (Meta mv2) =
    return $ mv1 == mv2
  synEq _ _ =
    return False


-- IsTerm
------------------------------------------------------------------------

class (Typeable t, Show t, Metas t t, Nf t t, PrettyM t t, ApplySubst t t, SynEq t t) => IsTerm t where
    -- Evaluation
    --------------------------------------------------------------------
    whnf :: MonadTerm t m => Term t -> m (Blocked (Term t))

    -- View / Unview
    --------------------------------------------------------------------

    -- | Note that nobody outside @Term/@ should use 'view' -- and in fact
    -- it's not exported from 'Term'.  Why?  Because you always want
    -- 'whnfView', that is a view with respect to the current signature.
    view   :: MonadTerm t m => Term t -> m (TermView t)

    -- | Similarly, nobody outside @Term/@ should use 'unview', but only
    -- the "smart constructors" below.  Why?  Resilience to future
    -- changes and more importantly we make lists of eliminators strict
    -- in the smart constructors.
    unview :: MonadTerm t m => TermView t -> m (Term t)

    -- We require these to be un-monadic mostly because having them
    -- monadic is a huge PITA when writing the type-checker/unifier.
    -- And, for 'typeOfJ', for performance reasons.
    set     :: Closed (Term t)
    refl    :: Closed (Term t)
    typeOfJ :: Closed (Type t)

whnfView :: (MonadTerm t m) => Term t -> m (TermView t)
whnfView t = (view <=< ignoreBlocking <=< whnf) t

-- | Representation of blocked terms.  Right now we just use 'Meta', but
-- in the future we want to support unistantiated functions too (see
-- Issue 5).
data Blocked t
  = NotBlocked t
  | BlockingHead Meta [Elim t]
  -- ^ The term is headed by some blocking thing.
  | BlockedOn MetaSet (BlockedHead t) [Elim t]
  -- ^ Some keys are preventing us from reducing a definition.  The
  -- 'BlockedHead' is the head, the 'Elim's the eliminators stuck on it.
  --
  -- Note that the metavariables impeding reduction might be both at
  -- the head of some eliminators, or impeding reduction of some other
  -- definition heading an eliminator.  In other words, even if the
  -- term is blocked, we don't guarantee that every eliminator is
  -- constructor headed.
 deriving (Eq, Show, Read, Typeable, Functor)

data BlockedHead t
    = BlockedOnFunction !(Opened QName t)
    | BlockedOnJ
    deriving (Eq, Show, Read, Typeable, Functor)

isBlocked :: Blocked t -> Maybe MetaSet
isBlocked (NotBlocked _)      = Nothing
isBlocked (BlockingHead mv _) = Just $ HS.singleton mv
isBlocked (BlockedOn mvs _ _) = Just mvs

ignoreBlocking :: (MonadTerm t m) => Blocked t -> m t
ignoreBlocking (NotBlocked t) =
  return t
ignoreBlocking (BlockingHead mv es) =
  meta mv es
ignoreBlocking (BlockedOn _ bh es) =
  let h = case bh of
            BlockedOnFunction fun -> Def fun
            BlockedOnJ            -> J
  in app h es

-- Term utils
-------------

seqList :: [a] -> b -> b
seqList []        x = x
seqList (!_ : xs) y = seqList xs y

var :: (MonadTerm t m) => Var -> m t
var v = app (Var v) []

lam :: (MonadTerm t m) => Abs t -> m t
lam body = unview $ Lam body

pi :: (MonadTerm t m) => t -> Abs t -> m t
pi domain codomain = unview $ Pi domain codomain

equal :: (MonadTerm t m) => t -> t -> t -> m t
equal type_ x y = unview $ Equal type_ x y

app :: (MonadTerm t m) => Head t -> [Elim t] -> m t
app h elims = seqList elims $ unview $ App h elims

meta :: (MonadTerm t m) => Meta -> [Elim t] -> m t
meta mv = app (Meta mv)

def :: (MonadTerm t m) => Opened QName t -> [Elim t] -> m t
def key = app (Def key)

con :: (MonadTerm t m) => Opened QName t -> [Term t] -> m t
con c args = seqList args $ unview $ Con c args

-- Clauses
------------------------------------------------------------------------

-- | A 'ClauseBody' scopes a term over a number of variables.  The
-- lowest number refers to the rightmost variable in the patterns, the
-- highest to the leftmost.
type ClauseBody t = t

-- | One clause of a function definition.
data Clause t = Clause [Pattern t] (ClauseBody t)
    deriving (Eq, Show, Read, Typeable, Functor)

data Pattern t
    = VarP
    | ConP (Opened QName t) [Pattern t]
    deriving (Eq, Show, Read, Typeable, Functor)

patternBindings :: Pattern t -> Natural
patternBindings VarP          = 1
patternBindings (ConP _ pats) = patternsBindings pats

patternsBindings :: [Pattern t] -> Natural
patternsBindings = sum . map patternBindings

-- Definition
------------------------------------------------------------------------

data Contextual t a = Contextual
  { contextualTelescope :: !(Tel t)
  , contextualInside    :: !a
  } deriving (Eq, Show, Typeable)

instance Bifunctor Contextual where
  bimap f g (Contextual tel t) = Contextual (fmap f tel) (g t)

-- TODO optimize this as we do in `genericWhnf`
openContextual
  :: (ApplySubst t a, MonadTerm t m, IsTerm t) => Contextual t a -> [Term t] -> m a
openContextual (Contextual tel t) args = do
  if telLength tel /= length args
    then __IMPOSSIBLE__
    else instantiate t args

ignoreContextual :: Contextual t a -> a
ignoreContextual (Contextual _ x) = x

type ContextualDef t = Contextual t (Definition Const t)

-- | A module, containing some names.  Note that once we reach
-- type-checking every name is fully qualified, so modules at these
-- stage are only opened so that we can instantiate their arguments.
type Module t = Contextual t (HS.HashSet QName)

data Definition f t
  = Constant (Type t) (Constant f t)
  | DataCon (f QName t) Natural (Contextual t (Type t))
  -- ^ Data type name, number of arguments, telescope ranging over the
  -- parameters of the type constructor ending with the type of the
  -- constructor.
  | Projection Field (f QName t) (Contextual t (Type t))
  -- ^ Field number, record type name, telescope ranging over the
  -- parameters of the type constructor ending with the type of the
  -- projected thing and finally the type of the projection.
  | Module (Module t)

deriving instance (Eq (Constant f t), Eq (f QName t), Eq t) => Eq (Definition f t)
deriving instance (Show (Constant f t), Show (f QName t), Show t) => Show (Definition f t)

openDefinition
  :: forall t m. (MonadTerm t m, IsTerm t)
  => ContextualDef t -> [Term t] -> m (Definition Opened t)
openDefinition ctxt args = do
  def' <- openContextual ctxt args
  return $ case def' of
    Constant type_ constant -> Constant type_ $ openConstant constant
    DataCon dataCon args' type_ -> DataCon (openName dataCon) args' type_
    Projection fld tyCon type_ -> Projection fld (openName tyCon) type_
    Module names -> Module names
  where
    openName :: Const a t -> Opened a t
    openName (Const n) = Opened n args

    openConstant Postulate = Postulate
    openConstant (Data dataCons) = Data $ map openName dataCons
    openConstant (Record dataCon projs) = Record (openName dataCon) (map openName projs)
    openConstant (Function inst) = Function inst

data Constant f t
  = Postulate
  | Data ![f QName t]
  -- ^ A data type, with constructors.
  | Record !(f QName t) ![f Projection t]
  -- ^ A record, with its constructor and projections.
  | Function !(FunInst t)
  -- ^ A function, which might be waiting for instantiation
#if __GLASGOW_HASKELL__ >= 708
  deriving (Typeable)
#endif

deriving instance (Eq (f QName t), Eq (f Projection t), Eq t) => Eq (Constant f t)
deriving instance (Show (f QName t), Show (f Projection t), Show t) => Show (Constant f t)

data FunInst t
  = Inst !(Invertible t)
  | Open
  deriving (Eq, Show, Typeable, Functor)

-- | A function is invertible if each of its clauses is headed by a
-- different 'TermHead'.
data Invertible t
  = NotInvertible [Clause t]
  | Invertible [(TermHead, Clause t)]
  -- ^ Each clause is paired with a 'TermHead' that doesn't happend
  -- anywhere else in the list.
  deriving (Eq, Show, Read, Typeable, Functor)

-- | A 'TermHead' is an injective type- or data-former.
data TermHead
  = PiHead
  | DefHead QName
  deriving (Eq, Show, Read)

instance PP.Pretty TermHead where
  pretty = PP.text . show

ignoreInvertible :: Invertible t -> [Clause t]
ignoreInvertible (NotInvertible clauses) = clauses
ignoreInvertible (Invertible injClauses) = map snd injClauses

definitionType :: (MonadTerm t m) => Closed (Definition n t) -> m (Closed (Type t))
definitionType (Constant type_ _) =
  return type_
definitionType (DataCon _ _ (Contextual tel type_)) =
  telPi tel type_
definitionType (Projection _ _ (Contextual tel type_)) =
  telPi tel type_
definitionType (Module _) =
  __IMPOSSIBLE__

-- 'Meta'iables
------------------------------------------------------------------------

-- | 'Meta'-variables.  Globally scoped.
data Meta = MV
  { metaId     :: !Int
  , metaSrcLoc :: !SrcLoc
  } deriving (Show, Read, Generic)

instance Eq Meta where
  (==) = (==) `on` metaId

instance Ord Meta where
  compare = comparing metaId

instance Hashable Meta where
  hashWithSalt s = hashWithSalt s . metaId

instance PP.Pretty Meta where
    prettyPrec _ (MV mv _) = PP.text $ "_" ++ show mv

instance HasSrcLoc Meta where
  srcLoc = metaSrcLoc

-- MonadTerm
------------------------------------------------------------------------

class (Functor m, Applicative m, Monad m, MonadIO m, IsTerm t) => MonadTerm t m | m -> t where
  askSignature :: m (Signature t)

newtype TermM t a = TermM (ReaderT (Signature t) IO a)
  deriving (Functor, Applicative, Monad, MonadIO)

instance (IsTerm t) => MonadTerm t (TermM t) where
  askSignature = TermM ask

runTermM :: Signature t -> TermM t a -> IO a
runTermM sig (TermM m) = runReaderT m sig

getDefinition :: (MonadTerm t m, IsTerm t) => Opened QName t -> m (Definition Opened t)
getDefinition n = do
  sig <- askSignature
  openDefinition (sigGetDefinition sig (opndKey n)) (opndArgs n)

getMetaType :: (MonadTerm t m) => Meta -> m (Type t)
getMetaType mv = (`sigGetMetaType` mv) <$> askSignature

lookupMetaBody :: (MonadTerm t m) => Meta -> m (Maybe (MetaBody t))
lookupMetaBody mv = (`sigLookupMetaBody` mv) <$> askSignature

-- getModule :: (MonadTerm t m) => QName -> m (Contextual t (HS.HashSet QName))
-- getModule n = (`sigGetModule` n) <$> askSignature

-- Signature
------------------------------------------------------------------------

data MetaBody t = MetaBody
  { mbArguments :: !Natural
    -- ^ The length of the context the meta lives in.
  , mbBody      :: !(Term t)
  } deriving (Eq, Show, Typeable)

metaBodyToTerm :: (MonadTerm t m) => MetaBody t -> m (Term t)
metaBodyToTerm (MetaBody args mvb) = go args
  where
    go 0 = return mvb
    go n = lam =<< go (n-1)

-- | A 'Signature' stores every globally scoped thing.
data Signature t = Signature
    { sigDefinitions    :: HMS.HashMap QName (ContextualDef t)
    , sigMetasTypes     :: HMS.HashMap Meta (Type t)
    , sigMetasBodies    :: HMS.HashMap Meta (MetaBody t)
      -- ^ Invariant: if a meta is present in 'sigMetasBodies', it's in
      -- 'sigMetasTypes'.
    , sigMetasCount     :: Int
    }

sigEmpty :: Signature t
sigEmpty = Signature HMS.empty HMS.empty HMS.empty 0

sigLookupDefinition :: Signature t -> QName -> Maybe (ContextualDef t)
sigLookupDefinition sig key = HMS.lookup key (sigDefinitions sig)

-- | Gets a definition for the given 'DefKey'.
sigGetDefinition :: Signature t -> QName -> Closed (ContextualDef t)
sigGetDefinition sig key = case HMS.lookup key (sigDefinitions sig) of
  Nothing   -> __IMPOSSIBLE__
  Just def' -> def'

sigAddDefinition :: Signature t -> QName -> ContextualDef t -> Signature t
sigAddDefinition sig key def' = case sigLookupDefinition sig key of
  Nothing -> sigInsertDefinition sig key def'
  Just _  -> __IMPOSSIBLE__

sigInsertDefinition :: Signature t -> QName -> ContextualDef t -> Signature t
sigInsertDefinition sig key def' =
  sig{sigDefinitions = HMS.insert key def' (sigDefinitions sig)}

sigAddPostulate :: Signature t -> QName -> Tel t -> Type t -> Signature t
sigAddPostulate sig name tel type_ =
  sigAddDefinition sig name $ Contextual tel $ Constant type_ Postulate

sigAddData :: Signature t -> QName -> Tel t -> Type t -> Signature t
sigAddData sig name tel type_ =
  sigAddDefinition sig name $ Contextual tel $ Constant type_ $ Data []

sigAddRecordCon :: Signature t -> Opened QName t -> QName -> Signature t
sigAddRecordCon sig name0 dataCon =
  case sigGetDefinition sig name of
    Contextual tel (Constant type_ Postulate) -> do
      sigInsertDefinition sig name $ Contextual tel $ Constant type_ $ Record (Const dataCon) []
    _ -> do
      __IMPOSSIBLE__
  where
    name = opndKey name0

sigAddTypeSig :: Signature t -> QName -> Tel t -> Type t -> Signature t
sigAddTypeSig sig name tel type_ =
  sigAddDefinition sig name $ Contextual tel $ Constant type_ $ Function Open

-- | We take an 'Opened QName t' because if we're adding clauses the
-- function declaration must already be opened.
sigAddClauses :: Signature t -> Opened QName t -> Invertible t -> Signature t
sigAddClauses sig name0 clauses =
  let name = opndKey name0
      def' = case sigGetDefinition sig name of
        Contextual tel (Constant type_ (Function Open)) ->
          Contextual tel $ Constant type_ $ Function $ Inst clauses
        _ ->
          __IMPOSSIBLE__
  in sigInsertDefinition sig name def'

sigAddProjection
  :: Signature t -> QName -> Field -> Opened QName t -> Contextual t (Type t) -> Signature t
sigAddProjection sig0 projName projIx tyCon0 ctxtType =
  case sigGetDefinition sig0 tyCon of
    Contextual tel (Constant tyConType (Record dataCon projs)) ->
      let def' = Contextual tel $ Projection projIx (Const tyCon) ctxtType
          sig  = sigAddDefinition sig0 projName def'
          projs' = projs ++ [Const (Projection' projName projIx)]
      in sigInsertDefinition sig tyCon $
         Contextual tel $ Constant tyConType (Record dataCon projs')
    _ ->
      __IMPOSSIBLE__
  where
    tyCon = opndKey tyCon0

sigAddDataCon
  :: Signature t -> QName -> Opened QName t -> Natural -> Contextual t (Type t) -> Signature t
sigAddDataCon sig0 dataConName tyCon0 numArgs ctxtType =
  case sigGetDefinition sig0 tyCon of
    Contextual tel (Constant tyConType (Data dataCons)) ->
      let sig = mkSig tel
          dataCons' = dataCons ++ [Const dataConName]
      in sigInsertDefinition sig tyCon $
         Contextual tel $ Constant tyConType (Data dataCons')
    -- With records, we must have already inserted the data constructor
    -- name using `sigAddRecordCon'
    Contextual tel' (Constant _ (Record _ _)) ->
      mkSig tel'
    _ ->
      __IMPOSSIBLE__
  where
    tyCon = opndKey tyCon0
    def' tel = Contextual tel $ DataCon (Const tyCon) numArgs ctxtType
    mkSig tel = sigAddDefinition sig0 dataConName $ def' tel

sigAddModule
  :: Signature t -> QName -> Tel t -> Module t -> Signature t
sigAddModule sig n args names =
  sigAddDefinition sig n $ Contextual args $ Module names

-- | Gets the type of a 'Meta'.  Fails if the 'Meta' if not
-- present.
sigGetMetaType
  :: (IsTerm t) => Signature t -> Meta -> Closed (Type t)
sigGetMetaType sig mv = case HMS.lookup mv (sigMetasTypes sig) of
  Just type_ -> type_
  Nothing    -> __IMPOSSIBLE__

sigLookupMetaBody
  :: (IsTerm t) => Signature t -> Meta -> Maybe (MetaBody t)
sigLookupMetaBody sig mv = HMS.lookup mv (sigMetasBodies sig)

-- | Creates a new 'Meta' with the provided type.
sigAddMeta :: Signature t -> SrcLoc -> Closed (Type t) -> (Meta, Signature t)
sigAddMeta sig0 loc type_ =
  (mv, sig{sigMetasTypes = HMS.insert mv type_ (sigMetasTypes sig)})
  where
    mv = MV (sigMetasCount sig) loc
    sig = sig0{sigMetasCount = sigMetasCount sig0 + 1}

-- | Instantiates the given 'Meta' with the given body.  Fails if no
-- type is present for the 'Meta'.
sigInstantiateMeta :: Signature t -> Meta -> MetaBody t -> Signature t
sigInstantiateMeta sig mv t = case HMS.lookup mv (sigMetasTypes sig) of
  Just _  -> sig{sigMetasBodies = HMS.insert mv t (sigMetasBodies sig)}
  Nothing -> __IMPOSSIBLE__

sigDefinedNames :: Signature t -> [QName]
sigDefinedNames sig = HMS.keys $ sigDefinitions sig

sigDefinedMetas :: Signature t -> [Meta]
sigDefinedMetas sig = HMS.keys $ sigMetasTypes sig

-- Context
------------------------------------------------------------------------

-- | A 'Ctx' is a backwards list of named terms, each scoped over all
-- the previous ones.
data Ctx t
  = C0
  | !(Ctx t) :< !(Name, Type t)
  deriving (Eq, Show, Typeable)

instance Monoid (Ctx t) where
  mempty = C0

  ctx1 `mappend` C0              = ctx1
  ctx1 `mappend` (ctx2 :< type_) = (ctx1 `mappend` ctx2) :< type_

ctxSingleton :: Name -> t -> Ctx t
ctxSingleton name t = C0 :< (name, t)

ctxLength :: Ctx t -> Natural
ctxLength C0         = 0
ctxLength (ctx :< _) = 1 + ctxLength ctx

ctxWeaken :: (MonadTerm t m) => Natural -> Ctx t -> t -> m t
ctxWeaken ix ctx t = weaken ix (ctxLength ctx) t

ctxWeaken_ :: (MonadTerm t m) => Ctx t -> t -> m t
ctxWeaken_ = ctxWeaken 0

ctxLookupName :: (MonadTerm t m) => Name -> Ctx t -> m (Maybe (Var, t))
ctxLookupName n = go 0
  where
    go _ C0 =
      return Nothing
    go ix (ctx :< (n', type_)) =
      if n == n'
      then Just . (mkVar n ix, ) <$> weaken_ (ix + 1) type_
      else go (ix + 1) ctx

ctxLookupVar :: (MonadTerm t m) => Var -> Ctx t -> m (Maybe t)
ctxLookupVar v _ | varIndex v < 0 =
  error "lookupVar: negative argument"
ctxLookupVar v ctx0 =
  case go (varIndex v) ctx0 of
    Nothing    -> return Nothing
    Just type_ -> Just <$> weaken_ (varIndex v + 1) type_
  where
    go _ C0 =
      Nothing
    go i (ctx :< (_, type_)) =
      if i == 0
        then Just type_
        else go (i - 1) ctx

ctxGetVar :: (MonadTerm t m) => Var -> Closed (Ctx t) -> m t
ctxGetVar v ctx = do
  mbT <- ctxLookupVar v ctx
  case mbT of
    Nothing -> __IMPOSSIBLE__
    Just t  -> return t

-- | Collects all the variables in the 'Ctx'.
ctxVars :: forall t. (IsTerm t) => Ctx (Type t) -> [Var]
ctxVars = reverse . go 0
  where
    go _  C0                 = []
    go ix (ctx :< (name, _)) = mkVar name ix : go (ix + 1) ctx

-- | Creates a 'Pi' type containing all the types in the 'Ctx' and
-- terminating with the provided 't'.
ctxPi :: (MonadTerm t m) => Ctx (Type t) -> Type t -> m (Type t)
ctxPi ctx0 = go ctx0
  where
    go C0                   t = return t
    go (ctx :< (_n, type_)) t = go ctx =<< pi type_ t

-- | Creates a 'Lam' term with as many arguments there are in the
-- 'Ctx'.
ctxLam :: (MonadTerm t m) => Ctx (Type t) -> Term t -> m (Term t)
ctxLam ctx0 = go ctx0
  where
    go C0         t = return t
    go (ctx :< _) t = go ctx =<< lam t

ctxApp :: (MonadTerm t m) => m (Term t) -> Ctx (Type t) -> m (Term t)
ctxApp t ctx0 = do
  t' <- t
  eliminate t' . map Apply =<< mapM var (ctxVars ctx0)

-- Telescope
------------------------------------------------------------------------

-- | A 'Tel' is a list of types, each one ranging over the rest of the
-- list, and with something of at the end -- the inverse of a 'Ctx.Ctx',
-- plus the end element.
data Tel t
  = T0
  | (Name, Term t) :> Tel t
  deriving (Show, Read, Eq, Functor)

instance Monoid (Tel t) where
  mempty = T0

  T0 `mappend` tel2 = tel2
  (type_ :> tel1) `mappend` tel2 = type_ :> (tel1 `mappend` tel2)

telLength :: Tel t -> Natural
telLength T0         = 0
telLength (_ :> tel) = 1 + telLength tel

-- Instances
----------------------

-- To/from Ctx
--------------

ctxToTel :: Ctx t -> Tel t
ctxToTel ctx0 = go ctx0 T0
  where
    go C0             tel = tel
    go (ctx :< type_) tel = go ctx (type_ :> tel)

telToCtx :: Tel t -> Ctx t
telToCtx tel0 = go C0 tel0
  where
    go ctx T0             = ctx
    go ctx (type_ :> tel) = go (ctx :< type_) tel

telAppend :: Ctx t -> Tel t -> Tel t
telAppend C0             tel = tel
telAppend (ctx :< type_) tel = telAppend ctx (type_ :> tel)

instance ApplySubst t (Tel t) where
  safeApplySubst = go
    where
      go T0 _ = do
        return T0
      go ((n, type_) :> tel) rho = do
        type' <- safeApplySubst type_ rho
        tel' <- go tel (subLift 1 rho)
        return $ (n, type') :> tel'

-- | Instantiates an 'Tel' repeatedly until we get to the bottom of
-- it.  Fails If the length of the 'Tel' and the provided list don't
-- match.
telDischarge :: (MonadTerm t m) => Tel t -> Term t -> [Term t] -> m t
telDischarge tel' t args =
  if telLength tel' == length args
  then instantiate t args
  else error "Term.Telescope.discharge"

telPi :: (MonadTerm t m) => Tel (Type t) -> Type t -> m (Type t)
telPi = ctxPi . telToCtx

-- TODO make more efficient, we reverse twice!
telVars :: forall t. (IsTerm t) => Tel (Type t) -> [Var]
telVars = ctxVars . telToCtx

telApp :: (MonadTerm t m) => m (Term t) -> Tel (Type t) -> m (Term t)
telApp t tel = do
  t' <- t
  eliminate t' . map Apply =<< mapM var (telVars tel)

------------------------------------------------------------------------
-- Substitution
------------------------------------------------------------------------

-- Smart constructors
------------------------------------------------------------------------

subId :: Subst t
subId = Id

subSingleton :: (MonadTerm t m, IsTerm t) => Term t -> m (Subst t)
subSingleton t = subInstantiate t subId

subWeaken :: Natural -> Subst t -> Subst t
subWeaken 0 rho                = rho
subWeaken n (Weaken m rho)     = Weaken (n + m) rho
subWeaken n (Strengthen m rho) = case n - m of
                                   0         -> rho
                                   k | k > 0 -> Weaken k rho
                                   k         -> Strengthen k rho
subWeaken n rho                = Weaken n rho

subStrengthen :: Natural -> Subst t -> Subst t
subStrengthen 0 rho                = rho
subStrengthen n (Strengthen m rho) = Strengthen (m + n) rho
subStrengthen n (Weaken m rho)     = case n - m of
                                       0         -> rho
                                       k | k < 0 -> Strengthen k rho
                                       k         -> Weaken k rho
subStrengthen n rho                = Strengthen n rho

subInstantiate :: (MonadTerm t m, IsTerm t) => Term t -> Subst t -> m (Subst t)
subInstantiate t rho = do
  tView <- view t
  return $ case (tView, rho) of
    (App (Var v) [], Weaken m sgm) | varIndex v + 1 == m ->
      subWeaken (m-1) $ subLift 1 sgm
    _ ->
      Instantiate t rho

subLift :: Natural -> Subst t -> Subst t
subLift n _            | n < 0 = error "lift.impossible"
subLift 0 rho          = rho
subLift _ Id           = Id
subLift k (Lift n rho) = Lift (n + k) rho
subLift k rho          = Lift k rho

subNull :: Subst t -> Bool
subNull Id = True
subNull _  = False

-- Operations
------------------------------------------------------------------------

subDrop :: Natural -> Subst t -> Subst t
subDrop n rho                 | n <= 0 = rho
subDrop n Id                  = subWeaken n subId
subDrop n (Weaken m rho)      = subWeaken m (subDrop n rho)
subDrop n (Instantiate _ rho) = subDrop (n - 1) rho
subDrop n (Strengthen m rho)  = subDrop (n - m) rho
subDrop _ (Lift 0 _)          = error "drop.Lift"
subDrop n (Lift m rho)        = subWeaken 1 $ subDrop (n - 1) $ subLift (m - 1) rho

subChain
  :: (MonadTerm t m)
  => Subst t -> Subst t -> m (Subst t)
subChain = flip subCompose

subCompose
  :: (MonadTerm t m)
  => Subst t -> Subst t -> m (Subst t)
subCompose rho Id =
  return rho
subCompose Id  rho =
  return rho
subCompose rho (Weaken n sgm) =
  subCompose (subDrop n rho) sgm
subCompose rho (Instantiate u sgm) =
  join $ subInstantiate <$> applySubst u rho <*> subCompose rho sgm
subCompose rho (Strengthen n sgm) =
  subStrengthen n <$> subCompose rho sgm
subCompose _ (Lift 0 _) =
  error "subCompose.Lift 0"
subCompose (Instantiate u rho) (Lift n sgm) =
  join $ subInstantiate u <$> subCompose rho (subLift (n - 1) sgm)
subCompose rho (Lift n sgm) =
  join $ subInstantiate <$> subUnsafeLookup (boundVar "_") rho
                        <*> subCompose rho (subWeaken 1 (subLift (n - 1) sgm))

subUnsafeLookup
  :: (MonadTerm t m) => Var -> Subst t -> m (Term t)
subUnsafeLookup v rho = do
  mbT <- runApplySubst $ subLookup v rho
  case mbT of
    Left n  -> error $ "unsafeLookup: free name " ++ show n
    Right t -> return t

subLookup :: forall t m. (MonadTerm t m) => Var -> Subst t -> ApplySubstM m (Term t)
subLookup v0 rho0 = go rho0 (varIndex v0)
  where
    nm = varName v0

    go :: Subst t -> Natural -> ApplySubstM m (Term t)
    go rho i = case rho of
      Id -> do
        lift $ var v
      Weaken n Id -> do
        let j = i + n
        lift $ var $ mkVar nm j
      Weaken n rho' -> do
        lift . (`applySubst` subWeaken n subId) =<< go rho' i
      Instantiate u rho' -> do
        if i == 0 then return u else go rho' (i - 1)
      Strengthen n rho' -> do
        if i >= n
          then go rho' (i - n)
          else throwE nm
      Lift n rho' -> do
        if i < n
          then lift $ var v
          else lift . (`applySubst` subWeaken n subId) =<< go rho' (i - n)
      where
        v = mkVar nm i

-- Operations on terms
------------------------------------------------------------------------

weaken :: (IsTerm t, ApplySubst t a, MonadTerm t m) => Natural -> Natural -> a -> m a
weaken from by t = applySubst t $ subLift from $ subWeaken by subId

weaken_ :: (IsTerm t, ApplySubst t a, MonadTerm t m) => Natural -> a -> m a
weaken_ n t = weaken 0 n t

strengthen :: (MonadTerm t m) => Natural -> Natural -> Abs t -> m t
strengthen from by t =
  applySubst t $ subLift from $ subStrengthen by subId

strengthen_ :: (MonadTerm t m) => Natural -> t -> m t
strengthen_ = strengthen 0

instantiate_ :: (IsTerm t, ApplySubst t a, MonadTerm t m) => a -> Term t -> m a
instantiate_ body arg = instantiate body [arg]

instantiate :: (IsTerm t , ApplySubst t a, MonadTerm t m) => a -> [Term t] -> m a
instantiate t0 ts0 = applySubst t0 =<< go (reverse ts0)
  where
    go []       = return subId
    go (t : ts) = subInstantiate t =<< go ts

safeStrengthen :: (IsTerm t, MonadTerm t m, ApplySubst t a) => a -> m (Maybe a)
safeStrengthen t = do
  nameOrT <- runApplySubst $ safeApplySubst t $ subStrengthen 1 subId
  case nameOrT of
    Left _   -> return Nothing
    Right t' -> return $ Just t'

getAbsName :: (MonadTerm t m) => Abs t -> m (Maybe Name)
getAbsName t = do
  skip <- confFastGetAbsName <$> readConf
  if skip
    then return (Just "_")
    else do
      nameOrT <- runApplySubst $ safeApplySubst t $ subStrengthen 1 subId
      case nameOrT of
        Right _ -> return Nothing
        Left n  -> return $ Just n

getAbsName_ :: (MonadTerm t m) => Abs t -> m Name
getAbsName_ t = fromMaybe "_" <$> getAbsName t

-- Elimination
------------------------------------------------------------------------

-- | Tries to apply the eliminators to the term.  Trows an error
-- when the term and the eliminators don't match.
eliminate :: (MonadTerm t m) => t -> [Elim t] -> m t
eliminate t elims = do
  reduce <- confWhnfEliminate <$> readConf
  tView <- if reduce then whnfView t else view t
  let badElimination = do
        tDoc <- prettyM t
        elimsDoc <- prettyM elims
        fatalError $ PP.render $
          "Bad elimination" $$
          "term:" //> tDoc $$
          "elims:" //> elimsDoc
  case (tView, elims) of
    (_, []) ->
        return t
    (Con _c args, Proj proj : es) -> do
        let ix = pField $ opndKey proj
        if unField ix >= length args
          then badElimination
          else eliminate (args !! unField ix) es
    (Lam body, Apply argument : es) -> do
        body' <- instantiate_ body argument
        eliminate body' es
    (App h es1, es2) ->
        app h (es1 ++ es2)
    (_, _) ->
        badElimination


{-
data OpenedItem t = OpenedItem
  { oiArguments :: ![Term t]
  , oiWeakenBy  :: !Natural
  }

-- | Here we store definitions that have been opened -- specifically, if
-- some definition is under a context with n variables, its entry here
-- should contain the n terms to apply to it to eliminate the context.
data Opened t
  = ONil
  | OSnoc (Opened t)
          -- The number of abstractions we went past to get to this point.
          !Natural
          -- The things we've opened -- note that we don't have
          -- 'Contextual' anymore.
          !(HMS.HashMap Name (Definition t))
-}

-- Clauses invertibility
------------------------

termHead :: (IsTerm t, MonadTerm t m) => t -> m (Maybe TermHead)
termHead t = do
  tView <- whnfView t
  case tView of
    App (Def opnd) _ -> do
      let f = opndKey opnd
      fDef <- getDefinition opnd
      return $ case fDef of
        Constant _ Data{}      -> Just $ DefHead f
        Constant _ Record{}    -> Just $ DefHead f
        Constant _ Postulate{} -> Just $ DefHead f
        Constant _ Function{}  -> Nothing
        DataCon{}              -> Nothing
        Projection{}           -> Nothing
        Module{}               -> __IMPOSSIBLE__
    App{} -> do
      return Nothing
    Con f _ ->
      return $ Just $ DefHead $ opndKey f
    Pi{} ->
      return $ Just $ PiHead
    Lam{} ->
      return Nothing
    Refl{} ->
      return Nothing
    Set{} ->
      return Nothing
    Equal{} ->
      return Nothing

checkInvertibility
  :: (IsTerm t, MonadTerm t m) => [Closed (Clause t)] -> m (Closed (Invertible t))
checkInvertibility = go []
  where
    go injClauses [] =
      return $ Invertible $ reverse injClauses
    go injClauses (clause@(Clause _ body) : clauses) = do
      th <- termHead body
      case th of
        Just tHead | Nothing <- lookup tHead injClauses ->
          go ((tHead, clause) : injClauses) clauses
        _ ->
          return $ NotInvertible $ reverse (map snd injClauses) ++ (clause : clauses)
