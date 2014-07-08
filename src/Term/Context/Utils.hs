module Term.Context.Utils where

import           Data.Functor                     ((<$>))
import           Data.Void                        (absurd)

import           Syntax.Internal                  (Name)
import           Term.Var
import qualified Term.Class                       as Term
import           Term.Class                       (IsTerm)
import           Term.Context
import           Term.TermM

weaken :: (IsTerm t) => Ctx v0 t v -> t v0 -> TermM (t v)
weaken Empty        t = return t
weaken (Snoc ctx _) t = Term.weaken =<< weaken ctx t

lookupName :: IsTerm t => Name -> Ctx v0 t v -> TermM (Maybe (Var v, t v))
lookupName n ctx0 = go ctx0
  where
    -- Helper function so that we have the proof of equality when
    -- pattern matching the variable.
    go :: IsTerm t => Ctx v0 t v -> TermM (Maybe (Var v, t v))
    go Empty                  = return Nothing
    go (Snoc ctx (n', type_)) =
      if n == n'
      then Just . (boundVar n, ) <$> Term.weaken type_
      else do
        mbT <- go ctx
        case mbT of
          Nothing     -> return Nothing
          Just (v, t) -> Just . (F v, ) <$> Term.weaken t

lookupIx :: IsTerm t => Int -> Name -> Ctx v0 t v -> TermM (Maybe (Var v, t v))
lookupIx i0 name ctx0 = go i0 ctx0
  where
    -- Helper function so that we have the proof of equality when
    -- pattern matching the variable.
    go :: IsTerm t => Int -> Ctx v0 t v -> TermM (Maybe (Var v, t v))
    go _ Empty                 = return Nothing
    go i (Snoc ctx (_, type_)) =
      if i <= 0
      then Just . (boundVar name, ) <$> Term.weaken type_
      else do
        mbT <- go (i - 1) ctx
        case mbT of
          Nothing     -> return Nothing
          Just (v, t) -> Just . (F v, ) <$> Term.weaken t

getVar :: forall t v. (IsTerm t) => Var v -> ClosedCtx t v -> TermM (t v)
getVar v0 ctx0 = go ctx0 v0
  where
    go :: forall v'. ClosedCtx t v' -> Var v' -> TermM (t v')
    go Empty               v     = return $ elimZeroVar v
    go (Snoc _ (_, type_)) (B _) = Term.weaken type_
    go (Snoc ctx _)        (F v) = Term.weaken =<< go ctx v

