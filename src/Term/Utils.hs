module Term.Utils where

import           Prelude                          hiding (pi)

import           Prelude.Extended
import           Term.Types
import           Term.MonadTerm
import qualified Term.Signature                   as Sig

instantiateMetaVars
  :: forall t m. (IsTerm t, MonadTerm t m)
  => t -> m t
instantiateMetaVars t = do
  tView <- view t
  sig <- askSignature
  case tView of
    Lam abs' ->
      lam abs'
    Pi dom cod ->
      join $ pi <$> instantiateMetaVars dom <*> instantiateMetaVars cod
    Equal type_ x y ->
      join $ equal <$> instantiateMetaVars type_
                   <*> instantiateMetaVars x
                   <*> instantiateMetaVars y
    Refl ->
      return refl
    Con dataCon ts ->
      con dataCon =<< mapM instantiateMetaVars ts
    Set ->
      return set
    App (Meta mv) els | Just t' <- Sig.getMetaVarBody sig mv -> do
      instantiateMetaVars =<< eliminate t' els
    App h els ->
      app h =<< mapM goElim els
  where
    goElim (Proj p)   = return $ Proj p
    goElim (Apply t') = Apply <$> instantiateMetaVars t'
