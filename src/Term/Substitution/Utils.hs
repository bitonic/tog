module Term.Substitution.Utils
  ( -- * Term operations through 'Substitution'
    weaken
  , weaken_
  , strengthen
  , strengthen_
  , subst
  , instantiate
  , instantiate_
  , eliminate
  ) where

import           Term.Synonyms
import           Term.Types
import qualified Term.Substitution                as Sub

weaken :: (IsTerm t, MonadTerm t m) => Int -> Int -> t -> m t
weaken from by = applySubst $ Sub.lift from $ Sub.weaken by Sub.id

weaken_ :: (IsTerm t, MonadTerm t m) => Int -> t -> m t
weaken_ n t = weaken 0 n t

strengthen :: (IsTerm t, MonadTerm t m) => Int -> Int -> Abs t -> m t
strengthen from by =
  applySubst $ Sub.lift from $ Sub.strengthen by Sub.id

strengthen_ :: (IsTerm t, MonadTerm t m) => Int -> t -> m t
strengthen_ = strengthen 0

subst :: (IsTerm t, MonadTerm t m) => Int -> Term t -> Term t -> m (Term t)
subst v u = applySubst $ Sub.lift v $ Sub.singleton u

instantiate_ :: (IsTerm t, MonadTerm t m) => Abs t -> Term t -> m (Term t)
instantiate_ body arg = instantiate body [arg]

instantiate :: (IsTerm t, MonadTerm t m) => Term t -> [Term t] -> m (Term t)
instantiate = error "TODO instantiate"

-- Elimination
------------------------------------------------------------------------

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
        body' <- instantiate_ body argument
        eliminate body' es
    (App h es1, es2) ->
        app h (es1 ++ es2)
    (_, _) ->
        error $ "eliminate: Bad elimination"
