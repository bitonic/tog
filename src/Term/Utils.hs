module Term.Utils where

import           Prelude                          hiding (pi)

import           Prelude.Extended
import           Term.Types
import           Term.TermM
import qualified Term.Signature                   as Sig

instantiateMetaVars
  :: forall t. (IsTerm t)
  => Sig.Signature t -> t -> TermM t
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
      instantiateMetaVars sig =<< eliminate sig t' els
    App h els ->
      app h =<< mapM goElim els
  where
    go t' = instantiateMetaVars sig t'

    goElim (Proj n field) = return $ Proj n field
    goElim (Apply t')     = Apply <$> go t'
