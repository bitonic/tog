{-# LANGUAGE OverloadedStrings #-}
module Term.Class where

import qualified Data.HashSet                     as HS

import           Prelude.Extended
import           Syntax.Internal                  (Name, DefName(SimpleName))
import qualified Syntax.Internal                  as A
import qualified Text.PrettyPrint.Extended        as PP
import {-# SOURCE #-} qualified Term.Signature    as Sig
import {-# SOURCE #-} qualified Term.Telescope    as Tel
import           Term.MetaVar
import           Term.Synonyms
import           Term.TermM

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

elimZeroVar :: Var -> a
elimZeroVar = error "elimZeroVar"

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
    | Def DefName
    | J
    | Meta MetaVar
    deriving (Show, Eq, Generic)

instance Hashable Head

-- | 'Elim's are applied to 'Head's.  They're either arguments applied
-- to functions, or projections applied to records.
data Elim t
    = Apply t
    | Proj Name Field
    deriving (Eq, Show, Generic)

instance (Hashable t) => Hashable (Elim t)

mapElimM :: Monad m => (t -> m t) -> Elim t -> m (Elim t)
mapElimM f (Apply t)  = Apply `liftM` f t
mapElimM _ (Proj n f) = return $ Proj n f

foldElim :: (t -> a) -> (Name -> Field -> a) -> Elim t -> a
foldElim f _ (Apply t)  = f t
foldElim _ g (Proj n f) = g n f

-- instance Subst' Elim where
--     subst' (Apply t)      f = Apply <$> subst t f
--     subst' (Proj n field) _ = return $ Proj n field

-- | The 'TermView' lets us pattern match on terms.  The actual
-- implementation of terms might be different, but we must be able to
-- get a 'TermView' out of it.  See 'View'.
data TermView t
    = Lam (Abs t)
    | Pi t (Abs t)
    | Equal t t t
    | Refl
    | Con Name [t]
    | Set
    | App Head [Elim t]
    deriving (Eq, Generic, Show)

instance (Hashable t) => Hashable (TermView t)

-- Term typeclass
------------------------------------------------------------------------

-- MetaVars
-----------

metaVars :: (IsTerm t) => Sig.Signature t -> Term t -> TermM (HS.HashSet MetaVar)
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

class (Typeable t) => IsTerm t where
    termEq :: t -> t -> TermM Bool
    default termEq :: Eq t => t -> t -> TermM Bool
    termEq t1 t2 = return $ t1 == t2

    -- Abstraction related
    --------------------------------------------------------------------
    weaken
      :: Int
      -- ^ Weaken starting from this index..
      -> Int
      -- ^ ..by this much.
      -> t
      -> TermM t

    strengthen
      :: Int -> Int -> Abs t -> TermM (Maybe t)

    substs :: [(Int, t)] -> t -> TermM t

    -- abstract :: Var -> t -> TermM (Abs t)
    -- abstract v t = do
    --   t' <- weaken_ 1 t
    --   vt <- var $ boundVar $ varName v
    --   subst (varIndex v + 1) vt t'

    getAbsName :: Abs t -> TermM (Maybe Name)

    -- Evaluation
    --------------------------------------------------------------------
    whnf :: Sig.Signature t -> t -> TermM (Blocked t)
    nf   :: Sig.Signature t -> t -> TermM t

    -- View / Unview
    --------------------------------------------------------------------
    view   :: t -> TermM (TermView t)

    whnfView :: Sig.Signature t -> t -> TermM (TermView t)
    whnfView sig t = (view <=< ignoreBlocking <=< whnf sig) t

    unview :: TermView t -> TermM t

    set     :: Closed t
    refl    :: Closed t
    typeOfJ :: Closed t

weaken_ :: (IsTerm t) => Int -> t -> TermM t
weaken_ n t = weaken 0 n t

strengthen_ :: (IsTerm t) => Int -> t -> TermM (Maybe t)
strengthen_ = strengthen 0

subst :: (IsTerm t) => Int -> t -> t -> TermM t
subst ix arg = substs [(ix, arg)]

instantiate :: (IsTerm t) => Abs t -> t -> TermM t
instantiate t arg = do
  arg' <- weaken_ 1 arg
  t' <- subst 0 arg' t
  Just t'' <- strengthen_ 1 t'
  return t''

getAbsName_ :: (IsTerm t) => Abs t -> TermM Name
getAbsName_ t = fromMaybe "_" <$> getAbsName t

data Blocked t
    = NotBlocked t
    | MetaVarHead MetaVar [Elim t]
    -- ^ The term is 'MetaVar'-headed.
    | BlockedOn (HS.HashSet MetaVar) DefName [Elim t]
    -- ^ Returned when some 'MetaVar's are preventing us from reducing a
    -- definition.  The 'Name' is the name of the definition, the
    -- 'Elim's the eliminators stuck on it.
    --
    -- Note that if anything else prevents reduction we're going to get
    -- 'NotBlocked'.
   deriving (Eq, Show)

ignoreBlocking :: (IsTerm t) => Blocked t -> TermM t
ignoreBlocking (NotBlocked t)           = return t
ignoreBlocking (MetaVarHead mv es)      = metaVar mv es
ignoreBlocking (BlockedOn _ funName es) = app (Def funName) es

-- mapBlockingM :: (t v -> TermM (t' v)) -> Blocked t v -> TermM (Blocked t' v)
-- mapBlockingM = undefined

-- | Tries to apply the eliminators to the term.  Trows an error
-- when the term and the eliminators don't match.
eliminate :: (IsTerm t) => Sig.Signature t -> t -> [Elim t] -> TermM t
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

-- termEq'
--   :: (IsTerm t1, IsTerm t2)
--   => t1 v -> t2 v -> TermM Bool
-- termEq' t1 t2 = do
--   tView1 <- view t1
--   tView2 <- view t2
--   case (tView1, tView2) of
--     (Lam body1, Lam body2) ->
--       termEq' body1 body2
--     (Pi domain1 codomain1, Pi domain2 codomain2) ->
--       (&&) <$> termEq' domain1 domain2 <*> termEq' codomain1 codomain2
--     (Equal type1 x1 y1, Equal type2 x2 y2) ->
--       (&&) <$> ((&&) <$> termEq' type1 type2 <*> termEq' x1 x2)
--            <*> termEq' y1 y2
--     (App h1 els1, App h2 els2) ->
--       (h1 == h2 &&) <$> elimsEq els1 els2
--     (Set, Set) ->
--       return True
--     (Con dataCon1 args1, Con dataCon2 args2) | dataCon1 == dataCon2 ->
--       argsEq args1 args2
--     (Refl, Refl) ->
--       return True
--     (_, _) -> do
--       return False
--   where
--     elimsEq []           []           = return True
--     elimsEq (el1 : els1) (el2 : els2) = (&&) <$> elimEq el1 el2 <*> elimsEq els1 els2
--     elimsEq _            _            = return False

--     elimEq (Apply t1')  (Apply t2')  = termEq' t1' t2'
--     elimEq (Proj n1 f1) (Proj n2 f2) = return $ n1 == n2 && f1 == f2
--     elimEq _            _            = return False

--     argsEq []             []             = return True
--     argsEq (arg1 : args1) (arg2 : args2) = (&&) <$> termEq' arg1 arg2 <*> argsEq args1 args2
--     argsEq _              _              = return False

-- definitionEq'
--   :: (IsTerm t1, IsTerm t2)
--   => Definition t1 v -> Definition t2 v -> TermM Bool
-- definitionEq' def1 def2 = case (def1, def2) of
--   (Constant ck1 type1, Constant ck2 type2) ->
--     (ck1 == ck2 &&) <$> termEq' type1 type2
--   (DataCon dataCon1 type1, DataCon dataCon2 type2) ->
--     (dataCon1 == dataCon2 &&) <$> telEq' type1 type2
--   (Projection f1 n1 type1, Projection f2 n2 type2) ->
--     ((f1 == f2 && n1 == n2) &&) <$> telEq' type1 type2
--   (Function type1 body1, Function type2 body2) -> do
--     (&&) <$> termEq' type1 type2 <*> invertibleEq' body1 body2
--   (_, _) -> do
--     return False

-- telEq'
--   :: (IsTerm t1, IsTerm t2)
--   => Tel.IdTel t1 v -> Tel.IdTel t2 v -> TermM Bool
-- telEq' (Tel.Empty (Tel.Id t1)) (Tel.Empty (Tel.Id t2)) =
--   termEq' t1 t2
-- telEq' (Tel.Cons (_, type1) tel1) (Tel.Cons (_, type2) tel2) =
--   (&&) <$> termEq' type1 type2 <*> telEq' tel1 tel2
-- telEq' _ _ =
--   return False

-- invertibleEq'
--   :: forall t1 t2 v. (IsTerm t1, IsTerm t2)
--   => Invertible t1 v -> Invertible t2 v -> TermM Bool
-- invertibleEq' clauses01 clauses02 =
--   case (clauses01, clauses02) of
--     (NotInvertible clauses1, NotInvertible clauses2) ->
--       clausesEq' (map ((),) clauses1) (map ((), ) clauses2)
--     (Invertible clauses1, Invertible clauses2) ->
--       clausesEq' clauses1 clauses2
--     (_, _) ->
--       return False
--   where
--     clausesEq' :: Eq a => [(a, Clause t1 v)] -> [(a, Clause t2 v)] -> TermM Bool
--     clausesEq' [] [] =
--       return True
--     clausesEq' ((x1, Clause pats1 body1) : clauses1) ((x2, Clause pats2 body2) : clauses2)
--       | pats1 == pats2 && x1 == x2 =
--         (&&) <$> clauseBodyEq' body1 body2 <*> clausesEq' clauses1 clauses2
--     clausesEq' _ _ =
--       return False

--     clauseBodyEq' :: ClauseBody t1 v' -> ClauseBody t2 v' -> TermM Bool
--     clauseBodyEq' (CBNil t1) (CBNil t2) =
--       termEq' t1 t2
--     clauseBodyEq' (CBArg body1) (CBArg body2) = clauseBodyEq' body1 body2
--     clauseBodyEq' _ _ = return False

-- Term utils
-------------

var :: (IsTerm t) => Var -> TermM t
var v = app (Var v) []

lam :: (IsTerm t) => Abs t -> TermM t
lam body = unview $ Lam body

pi :: (IsTerm t) => t -> Abs t -> TermM t
pi domain codomain = unview $ Pi domain codomain

equal :: (IsTerm t) => t -> t -> t -> TermM t
equal type_ x y = unview $ Equal type_ x y

app :: (IsTerm t) => Head -> [Elim t] -> TermM t
app h elims = unview $ App h elims

metaVar :: (IsTerm t) => MetaVar -> [Elim t] -> TermM t
metaVar mv = unview . App (Meta mv)

def :: (IsTerm t) => Name -> [Elim t] -> TermM t
def f = unview . App (Def (SimpleName f))

con :: (IsTerm t) => Name -> [t] -> TermM t
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

-- -- Subst'
-- ------------------------------------------------------------------------

-- class Subst' t where
--   subst' :: (IsTerm f) => t f a -> (Var a -> TermM (f b)) -> TermM (t f b)

-- subst'Map
--   :: forall t f (a :: Nat) (b :: Nat).
--      (IsTerm f, Subst' t)
--   => (Var a -> Var b) -> t f a -> TermM (t f b)
-- subst'Map f t = subst' t (var . f)

-- -- TODO these are obviously very unsafe, I should have something better,
-- -- but I don't want them to live them in IO...

-- substVacuous :: (Subst t) => t Zero -> t a
-- substVacuous = unsafeCoerce

-- subst'Vacuous :: (Subst' t, Subst f) => t f Zero -> t f a
-- subst'Vacuous = unsafeCoerce

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

instantiateClauseBody :: (IsTerm t) => ClauseBody t -> [t] -> TermM t
instantiateClauseBody body args = substs (zip [0..] $ reverse args) body

-- Definition
------------------------------------------------------------------------

data Definition t
    = Constant ConstantKind (Type t)
    | DataCon Name (Tel.Tel (Type t)) (Type t)
    -- ^ Data type name, telescope ranging over the parameters of the
    -- type constructor ending with the type of the constructor.
    | Projection Field Name (Tel.Tel (Type t)) (Type t)
    -- ^ Field number, record type name, telescope ranging over the
    -- parameters of the type constructor ending with the type of the
    -- projection.
    | Function (Type t) (Invertible t)
    -- ^ Function type, clauses.
    deriving (Typeable)

data ConstantKind
  = Postulate
  -- ^ Note that 'Postulates' might not be forever, since we add clauses
  -- when we encounter them.
  | Data [Name]
  -- ^ A data type, with constructors.
  | Record Name [(Name, Field)]
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
--
-- TODO Also include postulates when we have them to be explicit.
data TermHead = PiHead | DefHead DefName
    deriving (Eq, Show)

ignoreInvertible :: Invertible t -> [Clause t]
ignoreInvertible (NotInvertible clauses) = clauses
ignoreInvertible (Invertible injClauses) = map snd injClauses

-- mapInvertible :: (Clause t v -> Clause t' v')
--               -> Invertible t v -> Invertible t' v'
-- mapInvertible f (NotInvertible clauses) = NotInvertible $ map f clauses
-- mapInvertible f (Invertible injClauses) = Invertible $ map (second f) injClauses

-- From A.Expr
------------------------------------------------------------------------

internalToTerm
  :: (IsTerm t) => t -> TermM A.Expr
internalToTerm t0 = do
  tView <- view t0
  case tView of
    Lam body -> A.Lam "_" <$> internalToTerm body
    Pi dom cod -> A.Pi "_" <$> internalToTerm dom <*> internalToTerm cod
    Equal type_ x y -> A.Equal <$> internalToTerm type_ <*> internalToTerm x <*> internalToTerm y
    Refl -> return $ A.Refl A.noSrcLoc
    Con dataCon args -> A.Con dataCon <$> mapM internalToTerm args
    Set -> return $ A.Set A.noSrcLoc
    App h args -> do
      let h' = case h of
            Var v -> A.TermVar (varIndex v) (varName v)
            Def f -> A.Def f
            J -> A.J A.noSrcLoc
            Meta mv -> A.TermMeta $ unMetaVar mv
      A.App h' <$> mapM (foldElim (\t -> A.Apply <$> internalToTerm t) (\n _ -> return $ A.Proj n)) args
