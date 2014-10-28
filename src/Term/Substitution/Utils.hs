module Term.Substitution.Utils
  ( -- * Term operations through 'Substitution'
    weaken
  , weaken_
  , strengthen
  , strengthen_
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
