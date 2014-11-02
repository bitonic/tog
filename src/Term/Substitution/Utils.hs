{-# LANGUAGE OverloadedStrings #-}
module Term.Substitution.Utils
  ( -- * Term operations through 'Substitution'
    weaken
  , weaken_
  , strengthen
  , strengthen_
  , instantiate
  , instantiate_
  , eliminate
  ) where

import           Term.Synonyms
import           Term.Types
import qualified Term.Substitution                as Sub

import qualified PrettyPrint                      as PP
import           PrettyPrint                      (($$), (//>))

weaken :: (IsTerm t, Subst t a, MonadTerm t m) => Int -> Int -> a -> m a
weaken from by t = applySubst t $ Sub.lift from $ Sub.weaken by Sub.id

weaken_ :: (IsTerm t, Subst t a, MonadTerm t m) => Int -> a -> m a
weaken_ n t = weaken 0 n t

strengthen :: (IsTerm t, MonadTerm t m) => Int -> Int -> Abs t -> m t
strengthen from by t =
  applySubst t $ Sub.lift from $ Sub.strengthen by Sub.id

strengthen_ :: (IsTerm t, MonadTerm t m) => Int -> t -> m t
strengthen_ = strengthen 0

instantiate_ :: (IsTerm t, Subst t a, MonadTerm t m) => a -> Term t -> m a
instantiate_ body arg = instantiate body [arg]

instantiate :: (IsTerm t , Subst t a, MonadTerm t m) => a -> [Term t] -> m a
instantiate t0 ts0 = applySubst t0 $ go $ reverse ts0
  where
    go []       = Sub.id
    go (t : ts) = Sub.instantiate t (go ts)

-- Elimination
------------------------------------------------------------------------

-- | Tries to apply the eliminators to the term.  Trows an error
-- when the term and the eliminators don't match.
eliminate :: (IsTerm t, MonadTerm t m) => t -> [Elim t] -> m t
eliminate t elims = do
  tView <- whnfView t
  let badElimination = do
        tDoc <- prettyM t
        elimsDoc <- prettyM elims
        error $ PP.render $
          "Bad elimination" $$
          "term:" //> tDoc $$
          "elims:" //> elimsDoc
  case (tView, elims) of
    (_, []) ->
        return t
    (Con _c args, Proj proj : es) ->
        if unField (pField proj) >= length args
        then badElimination
        else eliminate (args !! unField (pField proj)) es
    (Lam body, Apply argument : es) -> do
        body' <- instantiate_ body argument
        eliminate body' es
    (App h es1, es2) ->
        app h (es1 ++ es2)
    (_, _) ->
        badElimination
