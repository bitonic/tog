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
  , Field(..)
    -- * Term typeclasses
    -- ** MetaVars
  , MetaVarSet
  , MetaVars(..)
  , MetaVar(..)
    -- ** Nf
  , Nf(..)
    -- ** Pretty
  , PrettyM(..)
    -- ** Subst
  , Subst(..)
    -- ** SynEq
  , SynEq(..)
    -- * IsTerm
  , IsTerm(..)
  , whnfView
  , getAbsName
  , getAbsName_
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
  , metaVar
  , def
  , con
    -- * TermTraverse
  , TermTraverse(..)
  , TermTraverse'
  , TermTraverseT(..)
  , hoistTT
    -- * Definition
  , Definition(..)
  , ConstantKind(..)
  , ClauseBody
  , Clause(..)
  , Pattern(..)
  , patternBindings
  , patternsBindings
  , Invertible(..)
  , TermHead(..)
  , ignoreInvertible
  , definitionToNameInfo
    -- * MonadTerm
  , MonadTerm(..)
  , TermM
  , runTermM
    -- * Signature
  , Signature(..)
  ) where

import           Control.Monad.Trans.Reader       (ReaderT, runReaderT, ask)
import           Control.Monad.Trans.Class        (MonadTrans)
import qualified Data.HashSet                     as HS
import qualified Data.HashMap.Strict              as HMS

import           Conf
import           Prelude.Extended
import           Syntax
import qualified Syntax.Internal                  as SI
import qualified PrettyPrint                      as PP
import           PrettyPrint                      ((<+>))
import           Term.Telescope.Types             (Tel)
import           Term.Substitution.Types          (Substitution)
import           Term.Synonyms

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
    | Def !Name
    | J
    | Meta !MetaVar
    deriving (Show, Read, Eq, Generic)

instance Hashable Head

-- | 'Elim's are applied to 'Head's.  They're either arguments applied
-- to functions, or projections applied to records.
data Elim t
    = Apply !t
    | Proj !Projection
    deriving (Eq, Show, Read, Generic, Functor, Foldable, Traversable)

instance (Hashable t) => Hashable (Elim t)

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

-- MetaVars
-----------

type MetaVarSet = HS.HashSet MetaVar

class MetaVars t a where
  metaVars :: (IsTerm t, MonadTerm t m) => a -> m (HS.HashSet MetaVar)

instance MetaVars t (Elim t) where
  metaVars (Apply t) = metaVars t
  metaVars (Proj _)  = return mempty

instance MetaVars t a => MetaVars t [a] where
  metaVars xs = mconcat <$> mapM metaVars xs

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

class Subst t a where
  applySubst :: (IsTerm t, MonadTerm t m) => a -> Substitution t -> m a

instance Subst t (Elim t) where
  applySubst (Proj p)  _   = return $ Proj p
  applySubst (Apply t) sub = Apply <$> applySubst t sub

instance Subst t a => Subst t [a] where
  applySubst t rho = mapM (`applySubst` rho) t

-- SynEq
------------------------------------------------------------------------

class SynEq t a where
  synEq :: (IsTerm t, MonadTerm t m) => a -> a -> m Bool

instance SynEq t (Elim t) where
  synEq e1 e2 = case (e1, e2) of
    (Proj p1,  Proj p2)  -> return $ p1 == p2
    (Apply t1, Apply t2) -> synEq t1 t2
    (_,        _)        -> return False

instance SynEq t (Blocked t) where
  synEq blockedX blockedY = case (blockedX, blockedY) of
    (NotBlocked x, NotBlocked y) ->
      synEq x y
    (MetaVarHead mv1 els1, MetaVarHead mv2 els2) | mv1 == mv2 ->
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

class (Typeable t, Show t, MetaVars t t, Nf t t, PrettyM t t, Subst t t, SynEq t t) => IsTerm t where
    -- Evaluation
    --------------------------------------------------------------------
    whnf :: MonadTerm t m => Term t -> m (Blocked (Term t))

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

    -- TODO Consider having a partial applySubst instead
    --------------------------------------------------------------------
    canStrengthen :: (MonadTerm t m) => t -> m (Maybe Name)

whnfView :: (IsTerm t, MonadTerm t m) => Term t -> m (TermView t)
whnfView t = (view <=< ignoreBlocking <=< whnf) t

getAbsName :: (IsTerm t, MonadTerm t m) => Abs t -> m (Maybe Name)
getAbsName t = do
  skip <- confFastGetAbsName <$> readConf
  if skip then return (Just "_") else canStrengthen t

getAbsName_ :: (IsTerm t, MonadTerm t m) => Abs t -> m Name
getAbsName_ t = fromMaybe "_" <$> getAbsName t

data Blocked t
    = NotBlocked t
    | MetaVarHead MetaVar [Elim t]
    -- ^ The term is 'MetaVar'-headed.
    | BlockedOn MetaVarSet BlockedHead [Elim t]
    -- ^ Returned when some 'MetaVar's are preventing us from reducing a
    -- definition.  The 'BlockedHead' is the head, the 'Elim's the
    -- eliminators stuck on it.
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

isBlocked :: Blocked t -> Maybe MetaVarSet
isBlocked (NotBlocked _)      = Nothing
isBlocked (MetaVarHead mv _)  = Just $ HS.singleton mv
isBlocked (BlockedOn mvs _ _) = Just mvs

instance PP.Pretty BlockedHead where
  pretty = PP.text . show

ignoreBlocking :: (IsTerm t, MonadTerm t m) => Blocked t -> m t
ignoreBlocking (NotBlocked t)      = return t
ignoreBlocking (MetaVarHead mv es) = metaVar mv es
ignoreBlocking (BlockedOn _ bh es) =
  let h = case bh of
            BlockedOnFunction funName -> Def funName
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

metaVar :: (IsTerm t, MonadTerm t m) => MetaVar -> [Elim t] -> m t
metaVar mv = app (Meta mv)

def :: (IsTerm t, MonadTerm t m) => Name -> [Elim t] -> m t
def f = app (Def f)

con :: (IsTerm t, MonadTerm t m) => Name -> [t] -> m t
con c args = seqList args $ unview $ Con c args

-- TermTraverse
------------------------------------------------------------------------

-- | Useful 'Applicative' when traversing terms, and we want to either
-- succeed ('TTOK'), or fail ('TTFail'), or collect a bunch of metas
-- ('TTMetaVars').  See instance definition for semantics.
data TermTraverse err a
    = TTOK a
    | TTFail err
    | TTMetaVars MetaVarSet
    deriving (Functor, Foldable, Traversable)

type TermTraverse' = TermTraverse ()

instance Applicative (TermTraverse m) where
    pure = TTOK

    TTOK f          <*> TTOK x           = TTOK $ f x
    TTOK _          <*> TTMetaVars mvs   = TTMetaVars mvs
    TTOK _          <*> TTFail v         = TTFail v
    TTMetaVars mvs  <*> TTOK _           = TTMetaVars mvs
    TTMetaVars mvs1 <*> TTMetaVars mvs2  = TTMetaVars (mvs1 <> mvs2)
    TTMetaVars _    <*> TTFail v         = TTFail v
    TTFail v        <*> _                = TTFail v

instance Monad (TermTraverse err) where
  return = TTOK

  TTOK x         >>= f = f x
  TTFail err     >>= _ = TTFail err
  TTMetaVars mvs >>= _ = TTMetaVars mvs

newtype TermTraverseT err m a =
  TTT {runTermTraverseT :: m (TermTraverse err a)}
  deriving (Functor)

hoistTT :: (Monad m) => TermTraverse err a -> TermTraverseT err m a
hoistTT = TTT . return

instance (Functor m, Monad m) => Applicative (TermTraverseT err m) where
  pure  = return
  (<*>) = ap

instance Monad m => Monad (TermTraverseT err m) where
  return = TTT . return . pure

  TTT m >>= f = TTT $ do
    tt <- m
    case tt of
      TTOK x -> runTermTraverseT $ f x
      TTFail err -> return $ TTFail err
      TTMetaVars mvs -> return $ TTMetaVars mvs

instance MonadTrans (TermTraverseT err) where
  lift m = TTT $ liftM TTOK m

-- Clauses
------------------------------------------------------------------------

-- | A 'ClauseBody' scopes a term over a number of variables.  The
-- lowest number refers to the rightmost variable in the patterns, the
-- highest to the leftmost.
type ClauseBody t = t

-- | One clause of a function definition.
data Clause t = Clause [Pattern] (ClauseBody t)
    deriving (Typeable)

data Pattern
    = VarP
    | ConP Name [Pattern]
    deriving (Eq, Show)

patternBindings :: Pattern -> Int
patternBindings VarP          = 1
patternBindings (ConP _ pats) = patternsBindings pats

patternsBindings :: [Pattern] -> Int
patternsBindings = sum . map patternBindings

-- Definition
------------------------------------------------------------------------

data Definition t
    = Constant ConstantKind (Type t)
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
    | Function (Type t) (Invertible t)
    -- ^ Function type, clauses.
    deriving (Typeable)

data ConstantKind
  = Postulate
  | TypeSig
  -- ^ A 'TypeSig' is like a 'Postulate', but it can eventually be
  -- instantiated.
  | Data [Name]
  -- ^ A data type, with constructors.
  | Record Name [Projection]
  -- ^ A record, with its constructors and projections.
  deriving (Eq, Show, Typeable)

-- | A function is invertible if each of its clauses is headed by a
-- different 'TermHead'.
data Invertible t
  = NotInvertible [Clause t]
  | Invertible [(TermHead, Clause t)]
  -- ^ Each clause is paired with a 'TermHead' that doesn't happend
  -- anywhere else in the list.

-- | A 'TermHead' is an injective type- or data-former.
data TermHead
  = PiHead
  | DefHead Name
  deriving (Eq, Show)

instance PP.Pretty TermHead where
  pretty = PP.text . show

ignoreInvertible :: Invertible t -> [Clause t]
ignoreInvertible (NotInvertible clauses) = clauses
ignoreInvertible (Invertible injClauses) = map snd injClauses

definitionToNameInfo :: Name -> Definition t -> NameInfo
definitionToNameInfo n (Constant _ _)       = SI.DefName n 0
definitionToNameInfo n (DataCon _ args _ _) = SI.ConName n 0 $ fromIntegral args
definitionToNameInfo n (Projection _ _ _ _) = SI.ProjName n 0
definitionToNameInfo n (Function _ _)       = SI.DefName n 0

-- 'MetaVar'iables
------------------------------------------------------------------------

-- | 'MetaVar'iables.  Globally scoped.
data MetaVar = MetaVar
  { mvId     :: !Int
  , mvSrcLoc :: !SrcLoc
  } deriving (Show, Read, Generic)

instance Eq MetaVar where
  (==) = (==) `on` mvId

instance Ord MetaVar where
  compare = comparing mvId

instance Hashable MetaVar where
  hashWithSalt s = hashWithSalt s . mvId

instance PP.Pretty MetaVar where
    prettyPrec _ (MetaVar mv _) = PP.text $ "_" ++ show mv

instance HasSrcLoc MetaVar where
  srcLoc = mvSrcLoc

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

-- Signature
------------------------------------------------------------------------

-- | A 'Signature' stores every globally scoped thing.  That is,
-- 'Definition's and 'MetaVar's bodies and types.
data Signature t = Signature
    { sigDefinitions    :: HMS.HashMap Name (Closed (Definition t))
    , sigMetasTypes     :: HMS.HashMap MetaVar (Closed (Type t))
    , sigMetasBodies    :: HMS.HashMap MetaVar (Closed (Term t))
    -- ^ INVARIANT: Every 'MetaVar' in 'sMetaBodies' is also in
    -- 'sMetasTypes'.
    , sigMetasCount     :: Int
    }
