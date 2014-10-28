module Term.FreeVars
  ( FreeVars(..)
  , fvAll
  , freeVars
  ) where

import           Control.Applicative              ((<*>))
import           Data.Functor                     ((<$>))
import           Data.Monoid                      (Monoid, mappend, mempty, (<>), mconcat)
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
    lift :: (Var -> Maybe Var) -> (Var -> Maybe Var)
    lift f (V (Named n ix)) =
      if ix > 0
      then f $ V (Named n (ix - 1))
      else Nothing

    go :: (Var -> Maybe Var) -> t -> m FreeVars
    go strengthen' t0 = do
      tView <- whnfView t0
      case tView of
        Lam body ->
          go (lift strengthen') body
        Pi domain codomain ->
          (<>) <$> go strengthen' domain <*> go (lift strengthen') codomain
        Equal type_ x y ->
          mconcat <$> mapM (go strengthen') [type_, x, y]
        App (Var v) elims -> do
          let fvs = FreeVars (maybe Set.empty Set.singleton (strengthen' v)) Set.empty
          (fvs <>) <$> (mconcat <$> mapM (go strengthen') [t | Apply t <- elims])
        App (Meta _) elims -> do
          fvs <- mconcat <$> mapM (go strengthen') [t | Apply t <- elims]
          return FreeVars{fvRigid = Set.empty, fvFlexible = fvAll fvs}
        App (Def _) elims ->
          mconcat <$> mapM (go strengthen') [t | Apply t <- elims]
        App J elims ->
          mconcat <$> mapM (go strengthen') [t | Apply t <- elims]
        Set ->
          return mempty
        Refl ->
          return mempty
        Con _ args ->
          mconcat <$> mapM (go strengthen') args
