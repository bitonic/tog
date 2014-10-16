{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE OverloadedStrings #-}
module Term.Types
  ( -- * Var
    Var(..)
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
    -- * MetaVars
  , MetaVar(..)
    -- * Terms
  , TermView(..)
  , Projection(..)
  , Head(..)
  , Elim(..)
  , Field(..)
  , elimEq
  , elimsEq
    -- ** Metavars
  , metaVars
    -- * Term typeclass
  , IsTerm(..)
  , weaken_
  , strengthen_
  , subst
  , getAbsName
  , getAbsName_
  , eliminate
    -- ** Blocked
  , Blocked(..)
  , BlockedHead(..)
  , isBlocked
  , ignoreBlocking
  , blockedEq
    -- ** Substitutions and Actions
  , Substitution
  , TermAction(..)
  , applyAction
  , applyActions
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
    -- * Definition
  , Definition(..)
  , ConstantKind(..)
  , ClauseBody
  , Clause(..)
  , Pattern(..)
  , patternBindings
  , patternsBindings
  , instantiateClauseBody
  , Invertible(..)
  , TermHead(..)
  , ignoreInvertible
  , definitionToNameInfo
  ) where

import           Prelude                          hiding (pi)

import qualified Data.HashSet                     as HS

import           Conf
import           Prelude.Extended
import           Syntax.Internal                  (Name)
import qualified Syntax.Internal                  as A
import qualified PrettyPrint                      as PP
import {-# SOURCE #-} qualified Term.Telescope    as Tel
import           Term.Synonyms
import           Term.MonadTerm

-- Var
------------------------------------------------------------------------

newtype Var = V {unVar :: Named Int}
  deriving (Eq, Ord, Hashable)

varIndex :: Var -> Int
varIndex = unNamed . unVar

varName :: Var -> Name
varName = namedName . unVar

instance PP.Pretty Var where
  pretty v = PP.text $ show (varIndex v) ++ "#" ++ show (varName v)

instance Show Var where
  show = PP.render

boundVar :: Name -> Var
boundVar n = V $ named n 0

weakenVar :: Int -> Int -> Var -> Var
weakenVar from by (V (Named n ix)) =
  let ix' = if ix >= from
            then ix + by
            else ix
  in V $ Named n ix'

weakenVar_ :: Int -> Var -> Var
weakenVar_ = weakenVar 0

strengthenVar :: Int -> Int -> Var -> Maybe Var
strengthenVar from by (V (Named n ix)) =
  let ix' | ix < from      = Just ix
          | ix < from + by = Nothing
          | otherwise      = Just $ ix - by
  in V . Named n <$> ix'

strengthenVar_ :: Int -> Var -> Maybe Var
strengthenVar_ = strengthenVar 0

-- unvar :: (Named () -> a) -> (Var n -> a) -> Var (Suc n) -> a
-- unvar f _ (B n) = f n
-- unvar _ f (F v) = f v

-- Named
------------------------------------------------------------------------

named :: Name -> a -> Named a
named = Named

data Named a = Named
  { namedName :: Name
  , unNamed   :: a
  } deriving (Functor, Foldable, Traversable, Generic)

instance Eq a => Eq (Named a) where
  Named _ v1 == Named _ v2 = v1 == v2

instance Ord a => Ord (Named a) where
  Named _ v1 `compare` Named _ v2 = v1 `compare` v2

instance (Hashable a) => Hashable (Named a)

-- Record 'Field's
------------------------------------------------------------------------

-- | The field of a projection.
newtype Field = Field {unField :: Int}
    deriving (Eq, Ord, Show, Hashable)

-- Terms
------------------------------------------------------------------------

-- | A 'Head' heads a neutral term -- something which can't reduce
-- further.
data Head
    = Var Var
    | Def Name
    | J
    | Meta MetaVar
    deriving (Show, Eq, Generic)

instance Hashable Head

-- | 'Elim's are applied to 'Head's.  They're either arguments applied
-- to functions, or projections applied to records.
data Elim t
    = Apply t
    | Proj !Projection
    deriving (Eq, Show, Generic, Functor, Foldable, Traversable)

instance (Hashable t) => Hashable (Elim t)

data Projection = Projection'
  { pName  :: !Name
  , pField :: !Field
  } deriving (Eq, Show, Generic)

instance Hashable Projection

instance PP.Pretty Projection where
  pretty = PP.pretty . pName

elimEq :: (IsTerm t, MonadTerm t m) => Elim t -> Elim t -> m Bool
elimEq (Apply t1) (Apply t2) = termEq t1 t2
elimEq (Proj p1)  (Proj p2)  = return $ p1 == p2
elimEq _            _            = return False

elimsEq :: (IsTerm t, MonadTerm t m) => [Elim t] -> [Elim t] -> m Bool
elimsEq []           []           = return True
elimsEq (el1 : els1) (el2 : els2) = (&&) <$> elimEq el1 el2 <*> elimsEq els1 els2
elimsEq _            _            = return False

-- | The 'TermView' lets us pattern match on terms.  The actual
-- implementation of terms might be different, but we must be able to
-- get a 'TermView' out of it.  See 'View'.
data TermView t
    = Pi t (Abs t)
    | Lam (Abs t)
    | Equal t t t
    | Refl
    | Set
    | Con Name [t]
    | App Head [Elim t]
    deriving (Eq, Generic, Show)

instance (Hashable t) => Hashable (TermView t)

-- Term typeclass
------------------------------------------------------------------------

-- MetaVars
-----------

metaVars :: (IsTerm t, MonadTerm t m) => Term t -> m (HS.HashSet MetaVar)
metaVars t = do
  tView <- whnfView t
  case tView of
    Lam body           -> metaVars body
    Pi domain codomain -> (<>) <$> metaVars domain <*> metaVars codomain
    Equal type_ x y    -> mconcat <$> mapM metaVars [type_, x, y]
    App h elims        -> (<>) <$> metaVarsHead h <*> (mconcat <$> mapM metaVarsElim elims)
    Set                -> return mempty
    Refl               -> return mempty
    Con _ elims        -> mconcat <$> mapM metaVars elims
  where
    metaVarsElim (Apply t') = metaVars t'
    metaVarsElim (Proj _)   = return mempty

    metaVarsHead (Meta mv) = return $ HS.singleton mv
    metaVarsHead _         = return mempty

-- HasAbs
---------

class (Typeable t, Show t) => IsTerm t where
    termEq :: MonadTerm t m => t -> t -> m Bool
    default termEq :: (MonadTerm t m, Eq t) => t -> t -> m Bool
    termEq t1 t2 = return $ t1 == t2

    -- Abstraction related
    --------------------------------------------------------------------
    weaken
      :: (MonadTerm t m)
      => Int
      -- ^ Weaken starting from this index..
      -> Int
      -- ^ ..by this much.
      -> t
      -> m t

    strengthen
      :: MonadTerm t m => Int -> Int -> Abs t -> m (Maybe t)

    -- | Applies the substitution from left to right (first
    -- substitutes the first element, and so on).
    substs :: MonadTerm t m => Substitution t -> t -> m t

    instantiate :: (MonadTerm t m, IsTerm t) => Abs t -> t -> m t
    instantiate t arg = do
      arg' <- weaken_ 1 arg
      t' <- subst 0 arg' t
      Just t'' <- strengthen_ 1 t'
      return t''

    getAbsName' :: MonadTerm t m => Abs t -> m (Maybe Name)

    -- Evaluation
    --------------------------------------------------------------------
    whnf :: MonadTerm t m => t -> m (Blocked t)
    nf   :: MonadTerm t m => t -> m t

    -- View / Unview
    --------------------------------------------------------------------
    view   :: MonadTerm t m => t -> m (TermView t)

    whnfView :: MonadTerm t m => t -> m (TermView t)
    whnfView t = (view <=< ignoreBlocking <=< whnf) t

    unview :: MonadTerm t m => TermView t -> m t

    set     :: Closed t
    refl    :: Closed t
    typeOfJ :: Closed t

weaken_ :: (IsTerm t, MonadTerm t m) => Int -> t -> m t
weaken_ n t = weaken 0 n t

strengthen_ :: (IsTerm t, MonadTerm t m) => Int -> t -> m (Maybe t)
strengthen_ = strengthen 0

subst :: (IsTerm t, MonadTerm t m) => Int -> t -> t -> m t
subst ix arg = substs [(ix, arg)]

getAbsName :: (IsTerm t, MonadTerm t m) => Abs t -> m (Maybe Name)
getAbsName t = do
  skip <- confFastGetAbsName <$> readConf
  if skip then return (Just "_") else getAbsName' t

getAbsName_ :: (IsTerm t, MonadTerm t m) => Abs t -> m Name
getAbsName_ t = fromMaybe "_" <$> getAbsName t

data Blocked t
    = NotBlocked t
    | MetaVarHead MetaVar [Elim t]
    -- ^ The term is 'MetaVar'-headed.
    | BlockedOn (HS.HashSet MetaVar) BlockedHead [Elim t]
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

isBlocked :: Blocked t -> Maybe (HS.HashSet MetaVar)
isBlocked (NotBlocked _)      = Nothing
isBlocked (MetaVarHead mv _)  = Just $ HS.singleton mv
isBlocked (BlockedOn mvs _ _) = Just mvs

instance PP.Pretty BlockedHead where
  pretty = PP.text . show

ignoreBlocking :: (IsTerm t, MonadTerm t m) => Blocked t -> m t
ignoreBlocking (NotBlocked t)           = return t
ignoreBlocking (MetaVarHead mv es)      = metaVar mv es
ignoreBlocking (BlockedOn _ bh es) =
  let h = case bh of
            BlockedOnFunction funName -> Def funName
            BlockedOnJ                -> J
  in app h es

blockedEq
  :: (IsTerm t, MonadTerm t m) => Blocked t -> Blocked t -> m Bool
blockedEq blockedX blockedY = case (blockedX, blockedY) of
  (NotBlocked x, NotBlocked y) ->
    termEq x y
  (MetaVarHead mv1 els1, MetaVarHead mv2 els2) | mv1 == mv2 ->
    elimsEq els1 els2
  (BlockedOn mvs1 f1 els1, BlockedOn mvs2 f2 els2) | mvs1 == mvs2 && f1 == f2 ->
    elimsEq els1 els2
  (_, _) ->
    return False

-- | Tries to apply the eliminators to the term.  Trows an error
-- when the term and the eliminators don't match.
eliminate :: (IsTerm t, MonadTerm t m) => t -> [Elim t] -> m t
eliminate t elims = do
  tView <- whnfView t
  case (tView, elims) of
    (_, []) ->
        return t
    (Con _c args, Proj proj : es) ->
        if unField (pField proj) >= length args
        then error "eliminate: Bad elimination"
        else eliminate (args !! unField (pField proj)) es
    (Lam body, Apply argument : es) -> do
        body' <- instantiate body argument
        eliminate body' es
    (App h es1, es2) ->
        app h (es1 ++ es2)
    (_, _) ->
        error $ "eliminate: Bad elimination"

-- Term utils
-------------

var :: (IsTerm t, MonadTerm t m) => Var -> m t
var v = app (Var v) []

lam :: (IsTerm t, MonadTerm t m) => Abs t -> m t
lam body = unview $ Lam body

pi :: (IsTerm t, MonadTerm t m) => t -> Abs t -> m t
pi domain codomain = unview $ Pi domain codomain

equal :: (IsTerm t, MonadTerm t m) => t -> t -> t -> m t
equal type_ x y = unview $ Equal type_ x y

app :: (IsTerm t, MonadTerm t m) => Head -> [Elim t] -> m t
app h elims = unview $ App h elims

metaVar :: (IsTerm t, MonadTerm t m) => MetaVar -> [Elim t] -> m t
metaVar mv = unview . App (Meta mv)

def :: (IsTerm t, MonadTerm t m) => Name -> [Elim t] -> m t
def f = unview . App (Def f)

con :: (IsTerm t, MonadTerm t m) => Name -> [t] -> m t
con c args = unview (Con c args)

-- TermTraverse
------------------------------------------------------------------------

-- | Useful 'Applicative' when traversing terms, and we want to either
-- succeed ('TTOK'), or fail ('TTFail'), or collect a bunch of metas
-- ('TTMetaVars').  See instance definition for semantics.
data TermTraverse err a
    = TTOK a
    | TTFail err
    | TTMetaVars (HS.HashSet MetaVar)
    deriving (Functor, Foldable, Traversable)

instance Applicative (TermTraverse err) where
    pure = TTOK

    TTOK f          <*> TTOK x           = TTOK (f x)
    TTOK _          <*> TTMetaVars mvs   = TTMetaVars mvs
    TTOK _          <*> TTFail v         = TTFail v
    TTMetaVars mvs  <*> TTOK _           = TTMetaVars mvs
    TTMetaVars mvs1 <*> TTMetaVars mvs2  = TTMetaVars (mvs1 <> mvs2)
    TTMetaVars _    <*> TTFail v         = TTFail v
    TTFail v        <*> _                = TTFail v

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

instantiateClauseBody
  :: (IsTerm t, MonadTerm t m) => ClauseBody t -> [Term t] -> m (Term t)
instantiateClauseBody body args =
  substs (zip [0..] $ reverse args) body

-- Definition
------------------------------------------------------------------------

data Definition t
    = Constant ConstantKind (Type t)
    | DataCon Name Int (Tel.Tel (Type t)) (Type t)
    -- ^ Data type name, number of arguments, telescope ranging over the
    -- parameters of the type constructor ending with the type of the
    -- constructor.
    | Projection Field Name (Tel.Tel (Type t)) (Type t)
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

definitionToNameInfo :: A.Name -> Definition t -> A.NameInfo
definitionToNameInfo n (Constant _ _)       = A.DefName n 0
definitionToNameInfo n (DataCon _ args _ _) = A.ConName n 0 args
definitionToNameInfo n (Projection _ _ _ _) = A.ProjName n 0
definitionToNameInfo n (Function _ _)       = A.DefName n 0

-- 'MetaVar'iables
------------------------------------------------------------------------

-- | 'MetaVar'iables.  Globally scoped.
data MetaVar = MetaVar
  { mvId     :: !Int
  , mvSrcLoc :: !A.SrcLoc
  } deriving (Generic)

instance Eq MetaVar where
  (==) = (==) `on` mvId

instance Ord MetaVar where
  compare = comparing mvId

instance Hashable MetaVar where
  hashWithSalt s = hashWithSalt s . mvId

instance PP.Pretty MetaVar where
    prettyPrec _ = PP.text . show

instance Show MetaVar where
   show (MetaVar mv _) = "_" ++ show mv

instance A.HasSrcLoc MetaVar where
  srcLoc = mvSrcLoc

-- Substitutions and Actions
------------------------------------------------------------------------

type Substitution t = [(Int, Term t)]

data TermAction t
  = Substs (Substitution t)
  | Weaken Int Int
  | Strengthen Int Int
  -- ^ Will fail if it can't be strengthened.

applyAction
  :: (IsTerm t, MonadTerm t m) => TermAction t -> Term t -> m (Term t)
applyAction a t = case a of
  Substs sub         -> substs sub t
  Weaken from by     -> weaken from by t
  Strengthen from by -> do Just t' <- strengthen from by t
                           return t'

-- | Applies some actions, first one first.
applyActions
  :: (IsTerm t, MonadTerm t m) => [TermAction t] -> Term t -> m (Term t)
applyActions as t = foldlM (\t' a -> applyAction a t') t as
