module Term.FreeVars
  ( FreeVars(..)
  , fvAll
  , freeVars
  ) where

import           Prelude.Extended
import qualified Data.Set                         as Set

import           Term.Types

-- Free variables
------------------------------------------------------------------------

data FreeVars = FreeVars
  { fvRigid    :: Set.Set Var
  , fvFlexible :: Set.Set Var
  }

fvAll :: FreeVars -> Set.Set Var
fvAll fvs = fvRigid fvs <> fvFlexible fvs

instance Monoid FreeVars where
  mempty = FreeVars Set.empty Set.empty

  FreeVars rigid1 flex1 `mappend` FreeVars rigid2 flex2 =
    FreeVars (rigid1 `mappend` rigid2) (flex1 `mappend` flex2)

freeVars
  :: forall t m. (IsTerm t, MonadTerm t m)
  => t -> m FreeVars
freeVars = go Just
  where
    lift' :: (Var -> Maybe Var) -> (Var -> Maybe Var)
    lift' f v =
      if varIndex v > 0
      then f $ mkVar (varName v) (varIndex v - 1)
      else Nothing

    go :: (Var -> Maybe Var) -> t -> m FreeVars
    go strengthen' t0 = do
      tView <- whnfView t0
      case tView of
        Lam body ->
          go (lift' strengthen') body
        Pi impl dom cod -> do
          fvs1 <- go strengthen' impl
          fvs2 <- go (lift' strengthen') dom
          fvs3 <- go (lift' (lift' strengthen')) cod
          return $ mconcat [fvs1, fvs2, fvs3]
        Equal type_ x y ->
          mconcat <$> mapM (go strengthen') [type_, x, y]
        App (Var v) elims -> do
          let fvs = FreeVars (maybe Set.empty Set.singleton (strengthen' v)) Set.empty
          (fvs <>) <$> (mconcat <$> mapM goElim elims)
        App (Meta _) elims -> do
          fvs <- mconcat <$> mapM goElim elims
          return FreeVars{fvRigid = Set.empty, fvFlexible = fvAll fvs}
        App (Def _) elims ->
          mconcat <$> mapM goElim elims 
        App J elims ->
          mconcat <$> mapM goElim elims
        Set ->
          return mempty
        Refl ->
          return mempty
        Con _ args ->
          mconcat <$> mapM (go strengthen') args
      where
        goElim (Proj _)    = return mempty
        goElim (Apply i t) = (<>) <$> (go strengthen' i) <*> (go strengthen' t)  
