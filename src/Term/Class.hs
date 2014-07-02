{-# LANGUAGE OverloadedStrings #-}
module Term.Class where

import           Prelude                          hiding (pi, foldr)

import           Bound                            (Var(B, F), Bound, (>>>=))
import           Data.Foldable                    (Foldable)
import           Data.Functor                     ((<$>))
import           Data.Traversable                 (Traversable)
import           Prelude.Extras                   (Eq1((==#)))
import           Data.Void                        (Void)
import           Data.Monoid                      (mempty, (<>), mconcat)
import qualified Data.HashSet                     as HS
import           Data.Typeable                    (Typeable)
import           Data.Maybe                       (fromMaybe)
import           Control.Applicative              (Applicative, pure, (<*>))
import           Control.Monad                    (liftM, (<=<), join)

import           Syntax.Internal                  (DefName(SimpleName), Name)
import           Term.MetaVar
import qualified Term.Signature                   as Sig
import qualified Term.Telescope                   as Tel
import           Term.Subst
import           Term.TermM
import           Term.Var
import           Term.Definition
import           Term.Synonyms

-- Terms
------------------------------------------------------------------------

-- | A 'Head' heads a neutral term -- something which can't reduce
-- further.
data Head v
    = Var v
    | Def DefName
    | J
    | Meta MetaVar
    deriving (Show, Eq, Functor, Foldable, Traversable)

instance Eq1 Head

-- | 'Elim's are applied to 'Head's.  They're either arguments applied
-- to functions, or projections applied to records.
data Elim term v
    = Apply (term v)
    | Proj Name Field
    deriving (Show, Eq, Functor, Foldable, Traversable)

mapElimM :: Monad m => (t v -> m (t v')) -> Elim t v -> m (Elim t v')
mapElimM f (Apply t)  = Apply `liftM` f t
mapElimM _ (Proj n f) = return $ Proj n f

foldElim :: (t v -> a) -> (Name -> Field -> a) -> Elim t v -> a
foldElim f _ (Apply t)  = f t
foldElim _ g (Proj n f) = g n f

instance (Eq1 term) => Eq1 (Elim term) where
    Apply t1   ==# Apply t2   = t1 ==# t2
    Proj n1 f1 ==# Proj n2 f2 = n1 == n2 && f1 == f2
    _          ==# _          = False

instance Subst' Elim where
    subst' (Apply t)      f = Apply <$> subst t f
    subst' (Proj n field) _ = return $ Proj n field

instance Bound Elim where
    Apply t      >>>= f = Apply (t >>= f)
    Proj n field >>>= _ = Proj n field

-- | The 'TermView' lets us pattern match on terms.  The actual
-- implementation of terms might be different, but we must be able to
-- get a 'TermView' out of it.  See 'View'.
data TermView term v
    = Lam (Abs term v)
    | Pi (term v) (Abs term v)
    | Equal (term v) (term v) (term v)
    | Refl
    | Con Name [term v]
    | Set
    | App (Head v) [Elim term v]
    deriving (Functor, Foldable, Traversable)

instance (Eq v, Eq1 t) => Eq (TermView t v) where
    t1 == t2 = t1 ==# t2

instance (Eq1 term) => Eq1 (TermView term) where
    Lam body1 ==# Lam body2 =
        body1 ==# body2
    Pi domain1 codomain1 ==# Pi domain2 codomain2 =
        domain1 ==# domain2 && codomain1 ==# codomain2
    Equal type1 x1 y1 ==# Equal type2 x2 y2 =
        type1 ==# type2 && x1 ==# x2 && y1 ==# y2
-- TODO we should compare heads first.
    App h1 [] ==# App h2 [] =
        h1 == h2
    App h1 (el1 : els1) ==# App h2 (el2 : els2) =
       el1 ==# el2 && App h1 els1 ==# App h2 els2
    Set ==# Set =
        True
    _ ==# _ =
        False

type ClosedTermView term = TermView term Void

-- Term typeclass
------------------------------------------------------------------------

-- MetaVars
-----------

metaVars :: (IsTerm t) => Sig.Signature t -> t v -> TermM (HS.HashSet MetaVar)
metaVars sig t = do
  tView <- whnfView sig t
  case tView of
    Lam body           -> metaVars sig body
    Pi domain codomain -> (<>) <$> metaVars sig domain <*> metaVars sig codomain
    Equal type_ x y    -> mconcat <$> mapM (metaVars sig) [type_, x, y]
    App h elims        -> (<>) <$> metaVarsHead h <*> (mconcat <$> mapM metaVarsElim elims)
    Set                -> return mempty
    Refl               -> return mempty
    Con _ elims        -> mconcat <$> mapM (metaVars sig) elims
  where
    metaVarsElim (Apply t') = metaVars sig t'
    metaVarsElim (Proj _ _) = return mempty

    metaVarsHead (Meta mv) = return $ HS.singleton mv
    metaVarsHead _         = return mempty

-- HasAbs
---------

type Abs t v = t (TermVar v)

class (Subst t, Typeable t) => IsTerm t where
    termEq :: (Eq v) => t v -> t v -> TermM Bool
    default termEq :: (Eq1 t, Eq v) => t v -> t v -> TermM Bool
    termEq t1 t2 = return $ t1 ==# t2

    -- Abstraction related
    --------------------------------------------------------------------
    weaken :: t v -> TermM (Abs t v)
    weaken = substMap F

    strengthen :: Abs t v -> TermM (Maybe (t v))

    instantiate :: Abs t v -> t v -> TermM (t v)
    instantiate abs' t = subst abs' $ \v -> case v of
        B _  -> return $ t
        F v' -> var v'

    abstract :: (Eq v, VarName v) => v -> t v -> TermM (Abs t v)
    abstract v t = substMap f t
      where
        f v' = if v == v' then boundTermVar (varName v) else F v'

    getAbsName :: Abs t v -> TermM (Maybe Name)

    -- Evaluation
    --------------------------------------------------------------------
    whnf :: Sig.Signature t -> t v -> TermM (Blocked t v)
    nf   :: Sig.Signature t -> t v -> TermM (t v)

    -- View / Unview
    --------------------------------------------------------------------
    view   :: t v -> TermM (TermView t v)

    whnfView :: Sig.Signature t -> t v -> TermM (TermView t v)
    whnfView sig t = (view <=< ignoreBlocking <=< whnf sig) t

    unview :: TermView t v -> TermM (t v)

    set     :: t v
    refl    :: t v
    typeOfJ :: Closed t

getAbsName_ :: IsTerm t => Abs t v -> TermM Name
getAbsName_ t = fromMaybe "_" <$> getAbsName t

data Blocked t v
    = NotBlocked (t v)
    | MetaVarHead MetaVar [Elim t v]
    -- ^ The term is 'MetaVar'-headed.
    | BlockedOn (HS.HashSet MetaVar) DefName [Elim t v]
    -- ^ Returned when some 'MetaVar's are preventing us from reducing a
    -- definition.  The 'Name' is the name of the definition, the
    -- 'Elim's the eliminators stuck on it.
    --
    -- Note that if anything else prevents reduction we're going to get
    -- 'NotBlocked'.
    deriving (Eq)

instance Eq1 t => Eq1 (Blocked t) where
    NotBlocked t1 ==# NotBlocked t2 =
      t1 ==# t2
    MetaVarHead mv1 es1 ==# MetaVarHead mv2 es2 =
      mv1 == mv2 && and (zipWith (==#) es1 es2)
    BlockedOn mv1 n1 es1 ==# BlockedOn mv2 n2 es2 =
      mv1 == mv2 && n1 == n2 && and (zipWith (==#) es1 es2)
    _ ==# _ =
      False

ignoreBlocking :: (IsTerm t) => Blocked t v -> TermM (t v)
ignoreBlocking (NotBlocked t)           = return t
ignoreBlocking (MetaVarHead mv es)      = metaVar mv es
ignoreBlocking (BlockedOn _ funName es) = app (Def funName) es

mapBlockingM :: (t v -> TermM (t' v)) -> Blocked t v -> TermM (Blocked t' v)
mapBlockingM = undefined

-- | Tries to apply the eliminators to the term.  Trows an error
-- when the term and the eliminators don't match.
eliminate :: (IsTerm t) => Sig.Signature t -> t v -> [Elim t v] -> TermM (t v)
eliminate sig t elims = do
  tView <- whnfView sig t
  case (tView, elims) of
    (_, []) ->
        return t
    (Con _c args, Proj _ field : es) ->
        if unField field >= length args
        then error "eliminate: Bad elimination"
        else eliminate sig (args !! unField field) es
    (Lam body, Apply argument : es) -> do
        body' <- instantiate body argument
        eliminate sig body' es
    (App h es1, es2) ->
        app h (es1 ++ es2)
    (_, _) ->
        error $ "eliminate: Bad elimination"
termEq'
  :: (IsTerm t1, IsTerm t2, Eq v)
  => t1 v -> t2 v -> TermM Bool
termEq' t1 t2 = do
  tView1 <- view t1
  tView2 <- view t2
  case (tView1, tView2) of
    (Lam body1, Lam body2) ->
      termEq' body1 body2
    (Pi domain1 codomain1, Pi domain2 codomain2) ->
      (&&) <$> termEq' domain1 domain2 <*> termEq' codomain1 codomain2
    (Equal type1 x1 y1, Equal type2 x2 y2) ->
      (&&) <$> ((&&) <$> termEq' type1 type2 <*> termEq' x1 x2)
           <*> termEq' y1 y2
    (App h1 els1, App h2 els2) ->
      (h1 == h2 &&) <$> elimsEq els1 els2
    (Set, Set) ->
      return True
    (Con dataCon1 args1, Con dataCon2 args2) | dataCon1 == dataCon2 ->
      argsEq args1 args2
    (Refl, Refl) ->
      return True
    (_, _) -> do
      return False
  where
    elimsEq []           []           = return True
    elimsEq (el1 : els1) (el2 : els2) = (&&) <$> elimEq el1 el2 <*> elimsEq els1 els2
    elimsEq _            _            = return False

    elimEq (Apply t1')  (Apply t2')  = termEq' t1' t2'
    elimEq (Proj n1 f1) (Proj n2 f2) = return $ n1 == n2 && f1 == f2
    elimEq _            _            = return False

    argsEq []             []             = return True
    argsEq (arg1 : args1) (arg2 : args2) = (&&) <$> termEq' arg1 arg2 <*> argsEq args1 args2
    argsEq _              _              = return False

definitionEq'
  :: (IsTerm t1, IsTerm t2, Eq v)
  => Definition t1 v -> Definition t2 v -> TermM Bool
definitionEq' def1 def2 = case (def1, def2) of
  (Constant ck1 type1, Constant ck2 type2) ->
    (ck1 == ck2 &&) <$> termEq' type1 type2
  (DataCon dataCon1 type1, DataCon dataCon2 type2) ->
    (dataCon1 == dataCon2 &&) <$> telEq' type1 type2
  (Projection f1 n1 type1, Projection f2 n2 type2) ->
    ((f1 == f2 && n1 == n2) &&) <$> telEq' type1 type2
  (Function type1 body1, Function type2 body2) -> do
    (&&) <$> termEq' type1 type2 <*> invertibleEq' body1 body2
  (_, _) -> do
    return False

telEq'
  :: (IsTerm t1, IsTerm t2, Eq v)
  => Tel.IdTel t1 v -> Tel.IdTel t2 v -> TermM Bool
telEq' (Tel.Empty (Tel.Id t1)) (Tel.Empty (Tel.Id t2)) =
  termEq' t1 t2
telEq' (Tel.Cons (_, type1) tel1) (Tel.Cons (_, type2) tel2) =
  (&&) <$> termEq' type1 type2 <*> telEq' tel1 tel2
telEq' _ _ =
  return False

invertibleEq'
  :: (IsTerm t1, IsTerm t2, Eq v)
  => Invertible t1 v -> Invertible t2 v -> TermM Bool
invertibleEq' clauses01 clauses02 =
  case (clauses01, clauses02) of
    (NotInvertible clauses1, NotInvertible clauses2) ->
      clausesEq' (map ((),) clauses1) (map ((), ) clauses2)
    (Invertible clauses1, Invertible clauses2) ->
      clausesEq' clauses1 clauses2
    (_, _) ->
      return False
  where
    clausesEq' [] [] =
      return True
    clausesEq' ((x1, Clause pats1 body1) : clauses1) ((x2, Clause pats2 body2) : clauses2)
      | pats1 == pats2 && x1 == x2 =
        (&&) <$> termEq' body1 body2 <*> clausesEq' clauses1 clauses2
    clausesEq' _ _ =
      return False

instantiateMetaVars
  :: forall t v. (IsVar v, IsTerm t)
  => Sig.Signature t -> t v -> TermM (t v)
instantiateMetaVars sig t = do
  tView <- view t
  case tView of
    Lam abs' ->
      lam abs'
    Pi dom cod ->
      join $ pi <$> go dom <*> go cod
    Equal type_ x y ->
      join $ equal <$> go type_ <*> go x <*> go y
    Refl ->
      return refl
    Con dataCon ts ->
      con dataCon =<< mapM go ts
    Set ->
      return set
    App (Meta mv) els | Just t' <- Sig.getMetaVarBody sig mv -> do
      instantiateMetaVars sig =<< eliminate sig (substVacuous t') els
    App h els ->
      app h =<< mapM goElim els
  where
    go :: forall v'. (IsVar v') => t v' -> TermM (t v')
    go t' = instantiateMetaVars sig t'

    goElim (Proj n field) = return $ Proj n field
    goElim (Apply t')     = Apply <$> go t'

-- Term utils
-------------

lam :: IsTerm t => Abs t v -> TermM (t v)
lam body = unview $ Lam body

pi :: IsTerm t => t v -> Abs t v -> TermM (t v)
pi domain codomain = unview $ Pi domain codomain

equal :: IsTerm t => t v -> t v -> t v -> TermM (t v)
equal type_ x y = unview $ Equal type_ x y

app :: IsTerm t => Head v -> [Elim t v] -> TermM (t v)
app h elims = unview $ App h elims

metaVar :: IsTerm t => MetaVar -> [Elim t v] -> TermM (t v)
metaVar mv = unview . App (Meta mv)

def :: IsTerm t => Name -> [Elim t v] -> TermM (t v)
def f = unview . App (Def (SimpleName f))

con :: IsTerm t => Name -> [t v] -> TermM (t v)
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
