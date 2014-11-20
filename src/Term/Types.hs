{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE NoImplicitPrelude #-}
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
  , DefKeySet
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
  , meta
  , def
  , defName
  , con
    -- * Definition
  , DefKey(..)
  , Definition(..)
  , Constant(..)
  , Instantiable(..)
  , ClauseBody
  , Clause(..)
  , Pattern(..)
  , patternBindings
  , patternsBindings
  , Invertible(..)
  , TermHead(..)
  , ignoreInvertible
  , definitionToNameInfo
  , definitionType
    -- * MonadTerm
  , MonadTerm(..)
  , TermM
  , runTermM
    -- ** Operations
  , getDefinition
  , getDefinition_
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
  , sigAddMeta
  , sigInstantiateMeta
    -- ** Utils
  , sigToScope
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
  ) where

import           Control.Monad.Trans.Reader       (ReaderT, runReaderT, ask)
import qualified Data.HashSet                     as HS
import qualified Data.HashMap.Strict              as HMS
import qualified Data.Map.Strict                  as Map

import           Instrumentation
import           Prelude.Extended
import           Syntax
import qualified Syntax.Abstract                  as SA
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
data Head
    = Var !Var
    | Def !DefKey
    | J
    deriving (Show, Read, Eq, Generic)

instance Hashable Head

-- | 'Elim's are applied to 'Head's.  They're either arguments applied
-- to functions, or projections applied to records.
data Elim t
    = Apply !t
    | Proj !Projection
    deriving (Eq, Show, Read, Generic, Functor, Foldable, Traversable)

instance (Hashable t) => Hashable (Elim t)

isApply :: Elim (Term t) -> Maybe (Term t)
isApply (Apply v) = Just v
isApply Proj{}    = Nothing

isProj :: Elim (Term t) -> Maybe Projection
isProj Apply{}  = Nothing
isProj (Proj p) = Just p

data Projection = Projection'
  { pName  :: !Name
  , pField :: !Field
  } deriving (Show, Read, Eq, Ord, Generic)

instance Hashable Projection

instance PP.Pretty Projection where
  pretty = PP.pretty . pName

-- | The 'TermView' lets us pattern match on terms.  The actual
-- implementation of terms might be different, but we must be able to
-- get a 'TermView' out of it.  See 'View'.
data TermView t
    = Pi !t !(Abs t)
    | Lam !(Abs t)
    | Equal !(Type t) !t !t
    | Refl
    | Set
    | Con !Name [t]
    | App !Head [Elim t]
    deriving (Eq, Generic, Show)

instance (Hashable t) => Hashable (TermView t)

-- Term typeclasses
------------------------------------------------------------------------

-- Metas
-----------

type MetaSet = HS.HashSet Meta

class Metas t a where
  metas :: (IsTerm t, MonadTerm t m) => a -> m (HS.HashSet Meta)

instance Metas t (Elim t) where
  metas (Apply t) = metas t
  metas (Proj _)  = return mempty

instance Metas t a => Metas t [a] where
  metas xs = mconcat <$> mapM metas xs

-- Nf
------------------------------------------------------------------------

class Nf t a where
  nf :: (IsTerm t, MonadTerm t m) => a -> m a

instance Nf t (Elim t) where
  nf (Proj p)  = return $ Proj p
  nf (Apply t) = Apply <$> nf t

instance Nf t a => Nf t [a] where
  nf = mapM nf

-- Pretty
------------------------------------------------------------------------

class PrettyM t a where
  {-# MINIMAL prettyPrecM | prettyM #-}

  prettyPrecM :: (IsTerm t, MonadTerm t m) => Int -> a -> m PP.Doc
  prettyPrecM _ = prettyM

  prettyM :: (IsTerm t, MonadTerm t m) => a -> m PP.Doc
  prettyM = prettyPrecM 0

instance PrettyM t (Elim t) where
  prettyPrecM p (Apply t) = do
    tDoc <- prettyPrecM p t
    return $ PP.condParens (p > 0) $ "$" <+> tDoc
  prettyPrecM _ (Proj p) = do
    return $ "." <> PP.pretty (pName p)

instance PrettyM t a => PrettyM t [a] where
  prettyM x = PP.list <$> mapM prettyM x

-- Subst
------------------------------------------------------------------------

type ApplySubstM = ExceptT Name

runApplySubst :: ApplySubstM m a -> m (Either Name a)
runApplySubst = runExceptT

class ApplySubst t a where
  safeApplySubst :: (IsTerm t, MonadTerm t m) => a -> Subst t -> ApplySubstM m a

instance ApplySubst t (Elim t) where
  safeApplySubst (Proj p)  _   = return $ Proj p
  safeApplySubst (Apply t) sub = Apply <$> safeApplySubst t sub

instance ApplySubst t a => ApplySubst t [a] where
  safeApplySubst t rho = mapM (`safeApplySubst` rho) t

applySubst :: (IsTerm t, MonadTerm t m, ApplySubst t a) => a -> Subst t -> m a
applySubst x rho = do
  nameOrRes <- runExceptT $ safeApplySubst x rho
  case nameOrRes of
    Left name -> error $ "applySubst: couldn't strengthen because of " ++ show name
    Right res -> return res

-- SynEq
------------------------------------------------------------------------

class SynEq t a where
  synEq :: (IsTerm t, MonadTerm t m) => a -> a -> m Bool

instance SynEq t (Elim t) where
  synEq e1 e2 = case (e1, e2) of
    (Proj p1,  Proj p2)  -> return $ p1 == p2
    (Apply t1, Apply t2) -> synEq t1 t2
    (_,        _)        -> return False

instance (Hashable key, Eq key) => SynEq t (Blocked key t) where
  synEq blockedX blockedY = case (blockedX, blockedY) of
    (NotBlocked x, NotBlocked y) ->
      synEq x y
    (BlockingHead mv1 els1, BlockingHead mv2 els2) | mv1 == mv2 ->
      synEq els1 els2
    (BlockedOn mvs1 f1 els1, BlockedOn mvs2 f2 els2) | mvs1 == mvs2 && f1 == f2 ->
      synEq els1 els2
    (_, _) ->
      return False

instance SynEq t a => SynEq t [a] where
  synEq []       []       = return True
  synEq (x : xs) (y : ys) = (&&) <$> synEq x y <*> synEq xs ys
  synEq _        _        = return False

instance (SynEq t a, SynEq t b) => SynEq t (a, b) where
  synEq (x1, y1) (x2, y2) = do
    b <- synEq x1 x2
    if b then synEq y1 y2 else return False

-- HasAbs
---------

class (Typeable t, Show t, Metas t t, Nf t t, PrettyM t t, ApplySubst t t, SynEq t t) => IsTerm t where
    -- Evaluation
    --------------------------------------------------------------------
    whnf :: MonadTerm t m => Term t -> m (Blocked Meta (Term t))

    -- View / Unview
    --------------------------------------------------------------------
    view   :: MonadTerm t m => Term t -> m (TermView t)
    unview :: MonadTerm t m => TermView t -> m (Term t)

    -- We require these to be un-monadic mostly because having them
    -- monadic is a huge PITA when writing the type-checker/unifier.
    -- And, for 'typeOfJ', for performance reasons.
    set     :: Closed (Term t)
    refl    :: Closed (Term t)
    typeOfJ :: Closed (Type t)

whnfView :: (IsTerm t, MonadTerm t m) => Term t -> m (TermView t)
whnfView t = (view <=< ignoreBlocking <=< whnf) t

type DefKeySet = HS.HashSet DefKey

data Blocked key t
  = NotBlocked t
  | BlockingHead key [Elim t]
  -- ^ The term is headed by a blocking 'DefKey'.
  | BlockedOn (HS.HashSet key) BlockedHead [Elim t]
  -- ^ Returned when some uninstantiated 'Meta's or functions are
  -- preventing us from reducing a definition.  The 'BlockedHead' is
  -- the head, the 'Elim's the eliminators stuck on it.
  --
  -- Note that the metavariables impeding reduction might be both at
  -- the head of some eliminators, or impeding reduction of some other
  -- definition heading an eliminator.  In other words, even if the
  -- term is blocked, we don't guarantee that every eliminator is
  -- constructor headed.
 deriving (Eq, Show)

data BlockedHead
    = BlockedOnFunction Name
    | BlockedOnJ
    deriving (Eq, Show)

isBlocked :: (Eq key, Hashable key) => Blocked key t -> Maybe (HS.HashSet key)
isBlocked (NotBlocked _)      = Nothing
isBlocked (BlockingHead mv _) = Just $ HS.singleton mv
isBlocked (BlockedOn mvs _ _) = Just mvs

instance PP.Pretty BlockedHead where
  pretty = PP.text . show

ignoreBlocking :: (IsTerm t, MonadTerm t m) => Blocked Meta t -> m t
ignoreBlocking (NotBlocked t) =
  return t
ignoreBlocking (BlockingHead mv es) =
  meta mv es
ignoreBlocking (BlockedOn _ bh es) =
  let h = case bh of
            BlockedOnFunction funName -> Def $ DKName funName
            BlockedOnJ                -> J
  in app h es

-- Term utils
-------------

seqList :: [a] -> b -> b
seqList []        x = x
seqList (!_ : xs) y = seqList xs y

var :: (IsTerm t, MonadTerm t m) => Var -> m t
var v = app (Var v) []

lam :: (IsTerm t, MonadTerm t m) => Abs t -> m t
lam body = unview $ Lam body

pi :: (IsTerm t, MonadTerm t m) => t -> Abs t -> m t
pi domain codomain = unview $ Pi domain codomain

equal :: (IsTerm t, MonadTerm t m) => t -> t -> t -> m t
equal type_ x y = unview $ Equal type_ x y

app :: (IsTerm t, MonadTerm t m) => Head -> [Elim t] -> m t
app h elims = seqList elims $ unview $ App h elims

meta :: (IsTerm t, MonadTerm t m) => Meta -> [Elim t] -> m t
meta mv = def (DKMeta mv)

def :: (IsTerm t, MonadTerm t m) => DefKey -> [Elim t] -> m t
def key = app (Def key)

defName :: (IsTerm t, MonadTerm t m) => Name -> [Elim t] -> m t
defName name = def (DKName name)

con :: (IsTerm t, MonadTerm t m) => Name -> [t] -> m t
con c args = seqList args $ unview $ Con c args

-- Clauses
------------------------------------------------------------------------

-- | A 'ClauseBody' scopes a term over a number of variables.  The
-- lowest number refers to the rightmost variable in the patterns, the
-- highest to the leftmost.
type ClauseBody t = t

-- | One clause of a function definition.
data Clause t = Clause [Pattern] (ClauseBody t)
    deriving (Eq, Show, Read, Typeable)

data Pattern
    = VarP
    | ConP Name [Pattern]
    deriving (Eq, Show, Read)

patternBindings :: Pattern -> Int
patternBindings VarP          = 1
patternBindings (ConP _ pats) = patternsBindings pats

patternsBindings :: [Pattern] -> Int
patternsBindings = sum . map patternBindings

-- Definition
------------------------------------------------------------------------

data DefKey
  = DKMeta !Meta
  | DKName !Name
  deriving (Eq, Show, Read, Generic)

instance Hashable DefKey

data Definition t
  = Constant (Type t) (Constant t)
  | DataCon Name Natural (Tel (Type t)) (Type t)
  -- ^ Data type name, number of arguments, telescope ranging over the
  -- parameters of the type constructor ending with the type of the
  -- constructor.
  | Projection Field Name (Tel (Type t)) (Type t)
  -- ^ Field number, record type name, telescope ranging over the
  -- parameters of the type constructor ending with the type of the
  -- projection.
  --
  -- Note that the type of the projection is always a pi type from a
  -- member of the record type to the type of the projected thing.
  deriving (Typeable)

data Constant t
  = Postulate
  | Data [Name]
  -- ^ A data type, with constructors.
  | Record Name [Projection]
  -- ^ A record, with its constructor and projections.
  | Instantiable (Instantiable t)
  -- ^ A function or a metavar, which might be waiting for instantiation
  deriving (Eq, Show, Typeable)

-- | Two things are instantiable: Meta's and Functions.
data Instantiable t
  = OpenMeta
  | InstMeta (MetaBody t)
  | OpenFun
  | InstFun (Invertible t)
  deriving (Eq, Show, Read)

-- | A function is invertible if each of its clauses is headed by a
-- different 'TermHead'.
data Invertible t
  = NotInvertible [Clause t]
  | Invertible [(TermHead, Clause t)]
  -- ^ Each clause is paired with a 'TermHead' that doesn't happend
  -- anywhere else in the list.
  deriving (Eq, Show, Read, Typeable)

-- | A 'TermHead' is an injective type- or data-former.
data TermHead
  = PiHead
  | DefHead Name
  deriving (Eq, Show, Read)

instance PP.Pretty TermHead where
  pretty = PP.text . show

data MetaBody t = MetaBody
  { mbVars :: !Natural
  , mbBody :: !(Term t)
  } deriving (Eq, Show, Read)

metaBodyToTerm :: (IsTerm t, MonadTerm t m) => MetaBody t -> m (Term t)
metaBodyToTerm (MetaBody n0 body0) = go n0 body0
  where
    go 0 body = return body
    go n body = lam =<< go (n-1) body

ignoreInvertible :: Invertible t -> [Clause t]
ignoreInvertible (NotInvertible clauses) = clauses
ignoreInvertible (Invertible injClauses) = map snd injClauses

definitionToNameInfo :: Name -> Definition t -> NameInfo
definitionToNameInfo n (Constant _ _)       = SA.DefName n 0
definitionToNameInfo n (DataCon _ args _ _) = SA.ConName n 0 $ fromIntegral args
definitionToNameInfo n (Projection _ _ _ _) = SA.ProjName n 0

definitionType :: (IsTerm t, MonadTerm t m) => Closed (Definition t) -> m (Closed (Type t))
definitionType (Constant type_ _)         = return type_
definitionType (DataCon _ _ tel type_)    = telPi tel type_
definitionType (Projection _ _ tel type_) = telPi tel type_

-- 'Meta'iables
------------------------------------------------------------------------

-- | 'Meta'-variables.  Globally scoped.
data Meta = Meta
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
    prettyPrec _ (Meta mv _) = PP.text $ "_" ++ show mv

instance HasSrcLoc Meta where
  srcLoc = metaSrcLoc

-- MonadTerm
------------------------------------------------------------------------

class (Functor m, Applicative m, Monad m, MonadIO m) => MonadTerm t m | m -> t where
  askSignature :: m (Signature t)

newtype TermM t a = TermM (ReaderT (Signature t) IO a)
  deriving (Functor, Applicative, Monad, MonadIO)

instance MonadTerm t (TermM t) where
  askSignature = TermM ask

runTermM :: Signature t -> TermM t a -> IO a
runTermM sig (TermM m) = runReaderT m sig

getDefinition :: MonadTerm t m => DefKey -> m (Definition t)
getDefinition name = (`sigGetDefinition'` name) <$> askSignature

getDefinition_ :: MonadTerm t m => Name -> m (Definition t)
getDefinition_ name = (`sigGetDefinition` name) <$> askSignature

lookupMetaBody :: MonadTerm t m => Meta -> m (Maybe (MetaBody t))
lookupMetaBody mv = (`sigLookupMetaBody` mv) <$> askSignature

getMetaType :: MonadTerm t m => Meta -> m (Type t)
getMetaType mv = (`sigGetMetaType` mv) <$> askSignature

-- Signature
------------------------------------------------------------------------

-- | A 'Signature' stores every globally scoped thing.
data Signature t = Signature
    { sigDefinitions    :: HMS.HashMap DefKey (Definition t)
    , sigMetasCount     :: Int
    }

sigEmpty :: Signature t
sigEmpty = Signature HMS.empty 0

sigLookupDefinition' :: Signature t -> DefKey -> Maybe (Definition t)
sigLookupDefinition' sig key = HMS.lookup key (sigDefinitions sig)

sigLookupDefinition :: Signature t -> Name -> Maybe (Definition t)
sigLookupDefinition sig name = sigLookupDefinition' sig $ DKName name

-- | Gets a definition for the given 'DefKey'.
sigGetDefinition' :: Signature t -> DefKey -> Closed (Definition t)
sigGetDefinition' sig key = case HMS.lookup key (sigDefinitions sig) of
  Nothing   -> __IMPOSSIBLE__
  Just def' -> def'

sigGetDefinition :: Signature t -> Name -> Closed (Definition t)
sigGetDefinition sig name = sigGetDefinition' sig $ DKName name

sigAddDefinition :: Signature t -> DefKey -> Definition t -> Signature t
sigAddDefinition sig key def' = case sigLookupDefinition' sig key of
  Nothing -> sigInsertDefinition sig key def'
  Just _  -> __IMPOSSIBLE__

sigInsertDefinition :: Signature t -> DefKey -> Definition t -> Signature t
sigInsertDefinition sig key def' =
  sig{sigDefinitions = HMS.insert key def' (sigDefinitions sig)}

sigAddPostulate :: Signature t -> Name -> Type t -> Signature t
sigAddPostulate sig name type_ =
  sigAddDefinition sig (DKName name) $ Constant type_ Postulate

sigAddData :: Signature t -> Name -> Type t -> Signature t
sigAddData sig name type_ =
  sigAddDefinition sig (DKName name) $ Constant type_ $ Data []

sigAddRecordCon :: Signature t -> Name -> Name -> Signature t
sigAddRecordCon sig name dataCon =
  case sigGetDefinition sig name of
    Constant type_ Postulate -> do
      sigInsertDefinition sig (DKName name) $ Constant type_ $ Record dataCon []
    _ -> do
      __IMPOSSIBLE__

sigAddTypeSig :: Signature t -> Name -> Type t -> Signature t
sigAddTypeSig sig name type_ =
  sigAddDefinition sig (DKName name) $ Constant type_ $ Instantiable OpenFun

sigAddClauses :: Signature t -> Name -> Invertible t -> Signature t
sigAddClauses sig name clauses =
  let def' = case sigGetDefinition sig name of
        Constant type_ (Instantiable OpenFun) ->
          Constant type_ $ Instantiable $ InstFun clauses
        _ ->
          __IMPOSSIBLE__
  in sigInsertDefinition sig (DKName name) def'

sigAddProjection
  :: Signature t -> Name -> Field -> Name -> Tel (Type t) -> Type t -> Signature t
sigAddProjection sig0 projName projIx tyCon tel type_ =
  case sigGetDefinition sig tyCon of
    Constant tyConType (Record dataCon projs) ->
      let projs' = projs ++ [Projection' projName projIx]
      in sigInsertDefinition sig (DKName tyCon) (Constant tyConType (Record dataCon projs'))
    _ ->
      __IMPOSSIBLE__
  where
    key = DKName projName
    def' = Projection projIx tyCon tel type_
    sig = sigAddDefinition sig0 key def'

sigAddDataCon
  :: Signature t -> Name -> Name -> Natural -> Tel (Type t) -> Type t -> Signature t
sigAddDataCon sig0 dataConName tyCon numArgs tel type_ =
  case sigGetDefinition sig tyCon of
    Constant tyConType (Data dataCons) ->
      let dataCons' = dataCons ++ [dataConName]
      in sigInsertDefinition sig (DKName tyCon) (Constant tyConType (Data dataCons'))
    -- With records, we must have already inserted the data constructor
    -- name using `sigAddRecordCon'
    Constant _ (Record _ _) ->
      sig
    _ ->
      __IMPOSSIBLE__
  where
    key = DKName dataConName
    def' = DataCon tyCon numArgs tel type_
    sig = sigAddDefinition sig0 key def'

-- | Gets the type of a 'Meta'.  Fails if the 'Meta' if not
-- present.
sigGetMetaType :: Signature t -> Meta -> Closed (Type t)
sigGetMetaType sig mv = case sigGetDefinition' sig (DKMeta mv) of
  Constant type_ (Instantiable OpenMeta)     -> type_
  Constant type_ (Instantiable (InstMeta _)) -> type_
  _                                          -> __IMPOSSIBLE__  -- Wrong definition

-- | Gets the body of a 'Meta', if present.
sigLookupMetaBody :: Signature t -> Meta -> Maybe (MetaBody t)
sigLookupMetaBody sig mv = case sigLookupDefinition' sig (DKMeta mv) of
  Nothing                                         -> Nothing
  Just (Constant _ (Instantiable OpenMeta))       -> Nothing
  Just (Constant _ (Instantiable (InstMeta mvb))) -> Just mvb
  _                                               -> __IMPOSSIBLE__

-- | Creates a new 'Meta' with the provided type.
sigAddMeta :: Signature t -> SrcLoc -> Closed (Type t) -> (Meta, Signature t)
sigAddMeta sig0 loc type_ = (mv, sigAddDefinition sig (DKMeta mv) def')
  where
    mv = Meta (sigMetasCount sig) loc
    sig = sig0{sigMetasCount = sigMetasCount sig0 + 1}
    def' = Constant type_ (Instantiable OpenMeta)

-- | Instantiates the given 'Meta' with the given body.  Fails if no
-- type is present for the 'Meta'.
sigInstantiateMeta :: Signature t -> Meta -> MetaBody t -> Signature t
sigInstantiateMeta sig mv mvb = do
  let def' = case sigGetDefinition' sig (DKMeta mv) of
        Constant type_ (Instantiable OpenMeta) ->
          Constant type_ $ Instantiable $ InstMeta mvb
        _ ->
          __IMPOSSIBLE__
  sigInsertDefinition sig (DKMeta mv) def'

sigDefinedNames :: Signature t -> [Name]
sigDefinedNames sig = [n | DKName n <- HMS.keys $ sigDefinitions sig]

sigDefinedMetas :: Signature t -> [Meta]
sigDefinedMetas sig = [mv | DKMeta mv <- HMS.keys $ sigDefinitions sig]

sigToScope :: Signature t -> Scope
sigToScope sig = Scope $ Map.fromList $ map f $ sigDefinedNames sig
  where
    f n = (nameString n, definitionToNameInfo n (sigGetDefinition sig n))

-- Context
------------------------------------------------------------------------

-- | A 'Ctx' is a backwards list of named terms, each scoped over all
-- the previous ones.
data Ctx t
  = C0
  | !(Ctx t) :< (Name, Type t)

instance Monoid (Ctx t) where
  mempty = C0

  ctx1 `mappend` C0              = ctx1
  ctx1 `mappend` (ctx2 :< type_) = (ctx1 `mappend` ctx2) :< type_

ctxSingleton :: Name -> t -> Ctx t
ctxSingleton name t = C0 :< (name, t)

ctxLength :: Ctx t -> Natural
ctxLength C0         = 0
ctxLength (ctx :< _) = 1 + ctxLength ctx

ctxWeaken :: (IsTerm t, MonadTerm t m) => Natural -> Ctx t -> t -> m t
ctxWeaken ix ctx t = weaken ix (ctxLength ctx) t

ctxWeaken_ :: (IsTerm t, MonadTerm t m) => Ctx t -> t -> m t
ctxWeaken_ = ctxWeaken 0

ctxLookupName :: (IsTerm t, MonadTerm t m) => Name -> Ctx t -> m (Maybe (Var, t))
ctxLookupName n = go 0
  where
    go _ C0 =
      return Nothing
    go ix (ctx :< (n', type_)) =
      if n == n'
      then Just . (mkVar n ix, ) <$> weaken_ (ix + 1) type_
      else go (ix + 1) ctx

ctxLookupVar :: (IsTerm t, MonadTerm t m) => Var -> Ctx t -> m (Maybe t)
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

ctxGetVar :: (IsTerm t, MonadTerm t m) => Var -> Closed (Ctx t) -> m t
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
ctxPi :: (IsTerm t, MonadTerm t m) => Ctx (Type t) -> Type t -> m (Type t)
ctxPi ctx0 = go ctx0
  where
    go C0                   t = return t
    go (ctx :< (_n, type_)) t = go ctx =<< pi type_ t

-- | Creates a 'Lam' term with as many arguments there are in the
-- 'Ctx'.
ctxLam :: (IsTerm t, MonadTerm t m) => Ctx (Type t) -> Term t -> m (Term t)
ctxLam ctx0 = go ctx0
  where
    go C0         t = return t
    go (ctx :< _) t = go ctx =<< lam t

ctxApp :: (IsTerm t, MonadTerm t m) => m (Term t) -> Ctx (Type t) -> m (Term t)
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
  deriving (Show, Read, Eq)

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
telDischarge :: (IsTerm t, MonadTerm t m) => Tel t -> Term t -> [Term t] -> m t
telDischarge tel' t args =
  if telLength tel' == length args
  then instantiate t args
  else error "Term.Telescope.discharge"

telPi :: (IsTerm t, MonadTerm t m) => Tel (Type t) -> Type t -> m (Type t)
telPi = ctxPi . telToCtx

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
subWeaken n rho                  = Weaken n rho

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
  :: (IsTerm t, MonadTerm t m)
  => Subst t -> Subst t -> m (Subst t)
subChain = flip subCompose

subCompose
  :: (IsTerm t, MonadTerm t m)
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
  :: (IsTerm t, MonadTerm t m) => Var -> Subst t -> m (Term t)
subUnsafeLookup v rho = do
  mbT <- runApplySubst $ subLookup v rho
  case mbT of
    Left n  -> error $ "unsafeLookup: free name " ++ show n
    Right t -> return t

subLookup :: forall t m. (IsTerm t, MonadTerm t m) => Var -> Subst t -> ApplySubstM m (Term t)
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

strengthen :: (IsTerm t, MonadTerm t m) => Natural -> Natural -> Abs t -> m t
strengthen from by t =
  applySubst t $ subLift from $ subStrengthen by subId

strengthen_ :: (IsTerm t, MonadTerm t m) => Natural -> t -> m t
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

getAbsName :: (IsTerm t, MonadTerm t m) => Abs t -> m (Maybe Name)
getAbsName t = do
  skip <- confFastGetAbsName <$> readConf
  if skip
    then return (Just "_")
    else do
      nameOrT <- runApplySubst $ safeApplySubst t $ subStrengthen 1 subId
      case nameOrT of
        Right _ -> return Nothing
        Left n  -> return $ Just n

getAbsName_ :: (IsTerm t, MonadTerm t m) => Abs t -> m Name
getAbsName_ t = fromMaybe "_" <$> getAbsName t

-- Elimination
------------------------------------------------------------------------

-- | Tries to apply the eliminators to the term.  Trows an error
-- when the term and the eliminators don't match.
eliminate :: (IsTerm t, MonadTerm t m) => t -> [Elim t] -> m t
eliminate t elims = do
  tView <- whnfView t
  let badElimination = do
        tDoc <- prettyM t
        elimsDoc <- prettyM elims
        error $ PP.render $
          "Bad elimination" $$
          "term:" //> tDoc $$
          "elims:" //> elimsDoc
  case (tView, elims) of
    (_, []) ->
        return t
    (Con _c args, Proj proj : es) ->
        if unField (pField proj) >= length args
        then badElimination
        else eliminate (args !! unField (pField proj)) es
    (Lam body, Apply argument : es) -> do
        body' <- instantiate_ body argument
        eliminate body' es
    (App h es1, es2) ->
        app h (es1 ++ es2)
    (_, _) ->
        badElimination
