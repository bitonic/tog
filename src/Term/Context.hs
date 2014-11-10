{-# LANGUAGE NoImplicitPrelude #-}
module Term.Context
    ( -- * 'Ctx'
      Ctx(..)
    , singleton
    , length
    , (++)
    , weaken
    , weaken_
    , lookupName
    , lookupVar
    , getVar
    , vars
    , pi
    , lam
    , app
    ) where

import           Prelude.Extended                 hiding (length, (++))
import qualified Prelude.Extended                 as Prelude
import           Syntax
import           Term.Types                       (IsTerm, Var, MonadTerm)
import qualified Term.Types                       as Term
import           Term.Synonyms
import qualified Term.Substitution.Utils          as Term

-- Ctx
------------------------------------------------------------------------

-- | A 'Ctx' is a backwards list of named terms, each scoped over all
-- the previous ones.
data Ctx t where
    Empty :: Ctx t
    Snoc  :: Ctx t -> (Name, t) -> Ctx (Abs t)
    deriving (Eq, Typeable)

singleton :: Name -> t -> Ctx t
singleton name t = Snoc Empty (name, t)

length :: Ctx t -> Natural
length Empty        = 0
length (Snoc ctx _) = 1 + length ctx

(++) :: Ctx t -> Ctx t -> Ctx t
ctx1 ++ Empty                 = ctx1
ctx1 ++ (Snoc ctx2 namedType) = Snoc (ctx1 ++ ctx2) namedType

weaken :: (IsTerm t, MonadTerm t m) => Natural -> Ctx t -> t -> m t
weaken ix ctx t = Term.weaken ix (length ctx) t

weaken_ :: (IsTerm t, MonadTerm t m) => Ctx t -> t -> m t
weaken_ = weaken 0

lookupName :: (IsTerm t, MonadTerm t m) => Name -> Ctx t -> m (Maybe (Term.Var, t))
lookupName n = go 0
  where
    go _ Empty =
      return Nothing
    go ix (Snoc ctx (n', type_)) =
      if n == n'
      then Just . (Term.mkVar n ix, ) <$> Term.weaken_ (ix + 1) type_
      else go (ix + 1) ctx

lookupVar :: (IsTerm t, MonadTerm t m) => Term.Var -> Ctx t -> m (Maybe t)
lookupVar v _ | Term.varIndex v < 0 =
  error "lookupVar: negative argument"
lookupVar v ctx0 =
  case go (Term.varIndex v) ctx0 of
    Nothing    -> return Nothing
    Just type_ -> Just <$> Term.weaken_ (Term.varIndex v + 1) type_
  where
    go _ Empty =
      Nothing
    go i (Snoc ctx (_, type_)) =
      if i == 0
        then Just type_
        else go (i - 1) ctx

getVar :: (IsTerm t, MonadTerm t m) => Term.Var -> Closed (Ctx t) -> m t
getVar v ctx = do
  mbT <- lookupVar v ctx
  case mbT of
    Nothing -> error $ "getVar: " Prelude.++ show v Prelude.++ " not in scope."
    Just t  -> return t

-- | Collects all the variables in the 'Ctx'.
vars :: forall t. (IsTerm t) => Ctx (Type t) -> [Var]
vars = toList . go 0
  where
    go :: Natural -> Ctx (Type t) -> Bwd Var
    go _  Empty                = B0
    go ix (Snoc ctx (name, _)) = go (ix + 1) ctx :< Term.mkVar name ix

-- | Creates a 'Pi' type containing all the types in the 'Ctx' and
-- terminating with the provided 't'.
pi :: (IsTerm t, MonadTerm t m) => Ctx (Type t) -> Type t -> m (Type t)
pi Empty                  t = return t
pi (Snoc ctx (_n, type_)) t = pi ctx =<< Term.pi_ type_ t

-- | Creates a 'Lam' term with as many arguments there are in the
-- 'Ctx'.
lam :: (IsTerm t, MonadTerm t m) => Ctx (Type t) -> Term t -> m (Term t)
lam Empty        t = return t
lam (Snoc ctx _) t = lam ctx =<< Term.lam t

app :: (IsTerm t, MonadTerm t m) => m (Term t) -> Ctx (Type t) -> m (Term t)
app t ctx0 = do
  t' <- t
  Term.eliminate t' . map Term.Apply =<< mapM Term.var (vars ctx0)
