module Term.FreeVars
  ( FreeVars(..)
  , fvAll
  , freeVars
  ) where

import           Control.Applicative              ((<*>))
import           Data.Functor                     ((<$>))
import           Data.Monoid                      (Monoid, mappend, mempty, (<>), mconcat)
import qualified Data.Set                         as Set

import qualified Term.Signature                   as Sig
import           Term.Class
import           Term.Var
import           Term.TermM
import           Term.Nat

-- Free variables
------------------------------------------------------------------------

data FreeVars v = FreeVars
  { fvRigid    :: Set.Set (Var v)
  , fvFlexible :: Set.Set (Var v)
  }

fvAll :: FreeVars v -> Set.Set (Var v)
fvAll fvs = fvRigid fvs <> fvFlexible fvs

instance Monoid (FreeVars v) where
  mempty = FreeVars Set.empty Set.empty

  FreeVars rigid1 flex1 `mappend` FreeVars rigid2 flex2 =
    FreeVars (rigid1 `mappend` flex1) (rigid2 `mappend` flex2)

freeVars
  :: forall t v0. (IsTerm t)
  => Sig.Signature t -> t v0 -> TermM (FreeVars v0)
freeVars sig = go Just
  where
    lift :: (Var v -> Maybe (Var v0)) -> (Var (Suc v) -> Maybe (Var v0))
    lift _ (B _) = Nothing
    lift f (F v) = f v

    go :: (Var v -> Maybe (Var v0)) -> t v -> TermM (FreeVars v0)
    go strengthen' t0 = do
      tView <- whnfView sig t0
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
