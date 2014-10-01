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
    ) where

import           Prelude                          hiding (pi, length, lookup, (++))
import qualified Prelude

import           Prelude.Extended
import           Syntax.Internal                  (Name)
import qualified Term.Types                       as Term
import           Term.Synonyms
import           Term.MonadTerm

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

length :: Ctx t -> Int
length Empty        = 0
length (Snoc ctx _) = 1 + length ctx

(++) :: Ctx t -> Ctx t -> Ctx t
ctx1 ++ Empty                 = ctx1
ctx1 ++ (Snoc ctx2 namedType) = Snoc (ctx1 ++ ctx2) namedType

weaken :: (Term.IsTerm t, MonadTerm t m) => Int -> Ctx t -> t -> m t
weaken ix ctx t = Term.weaken ix (length ctx) t

weaken_ :: (Term.IsTerm t, MonadTerm t m) => Ctx t -> t -> m t
weaken_ = weaken 0

lookupName :: (Term.IsTerm t, MonadTerm t m) => Name -> Ctx t -> m (Maybe (Term.Var, t))
lookupName n = go 0
  where
    go _ Empty =
      return Nothing
    go ix (Snoc ctx (n', type_)) =
      if n == n'
      then Just . (Term.V (Term.named n ix), ) <$> Term.weaken_ (ix + 1) type_
      else go (ix + 1) ctx

lookupVar :: (Term.IsTerm t, MonadTerm t m) => Term.Var -> Ctx t -> m (Maybe t)
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

getVar :: (Term.IsTerm t, MonadTerm t m) => Term.Var -> Closed (Ctx t) -> m t
getVar v ctx = do
  mbT <- lookupVar v ctx
  case mbT of
    Nothing -> error $ "getVar: " Prelude.++ show v Prelude.++ " not in scope."
    Just t  -> return t

