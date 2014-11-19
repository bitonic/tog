{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE NoImplicitPrelude #-}
module Term.Subst.Utils
  ( -- * Term operations through 'Subst'
    weaken
  , weaken_
  , strengthen
  , strengthen_
  , instantiate
  , instantiate_
  , pi_
  , safeStrengthen
  , getAbsName
  , getAbsName_

  , eliminate
  ) where

import           Conf
import           Syntax
import           Prelude.Extended
import           Term.Synonyms
import           Term.Types
import qualified Term.Subst                as Sub
import qualified PrettyPrint                      as PP
import           PrettyPrint                      (($$), (//>))

weaken :: (IsTerm t, ApplySubst t a, MonadTerm t m) => Natural -> Natural -> a -> m a
weaken from by t = applySubst t $ Sub.lift from $ Sub.weaken by Sub.id

weaken_ :: (IsTerm t, ApplySubst t a, MonadTerm t m) => Natural -> a -> m a
weaken_ n t = weaken 0 n t

strengthen :: (IsTerm t, MonadTerm t m) => Natural -> Natural -> Abs t -> m t
strengthen from by t =
  applySubst t $ Sub.lift from $ Sub.strengthen by Sub.id

strengthen_ :: (IsTerm t, MonadTerm t m) => Natural -> t -> m t
strengthen_ = strengthen 0

instantiate_ :: (IsTerm t, ApplySubst t a, MonadTerm t m) => a -> Term t -> m a
instantiate_ body arg = instantiate body [arg]

instantiate :: (IsTerm t , ApplySubst t a, MonadTerm t m) => a -> [Term t] -> m a
instantiate t0 ts0 = applySubst t0 =<< go (reverse ts0)
  where
    go []       = return Sub.id
    go (t : ts) = Sub.instantiate t =<< go ts

safeStrengthen :: (IsTerm t, MonadTerm t m, ApplySubst t a) => a -> m (Maybe a)
safeStrengthen t = do
  nameOrT <- runApplySubst $ safeApplySubst t $ Sub.strengthen 1 Sub.id
  case nameOrT of
    Left _   -> return Nothing
    Right t' -> return $ Just t'

getAbsName :: (IsTerm t, MonadTerm t m) => Abs t -> m (Maybe Name)
getAbsName t = do
  skip <- confFastGetAbsName <$> readConf
  if skip
    then return (Just "_")
    else do
      nameOrT <- runApplySubst $ safeApplySubst t $ Sub.strengthen 1 Sub.id
      case nameOrT of
        Right _ -> return Nothing
        Left n  -> return $ Just n

getAbsName_ :: (IsTerm t, MonadTerm t m) => Abs t -> m Name
getAbsName_ t = fromMaybe "_" <$> getAbsName t

pi_ :: (IsTerm t, MonadTerm t m) => t -> (Abs t) -> m t
pi_ dom cod = join $ pi top <$> weaken_  1 dom <*> weaken 1 1 cod 

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
    (Lam body, Apply impl argument : es) -> do
        body' <- instantiate body [impl,argument]
        eliminate body' es
    (App h es1, es2) ->
        app h (es1 ++ es2)
    (_, _) ->
        badElimination
