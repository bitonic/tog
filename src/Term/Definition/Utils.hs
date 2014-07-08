module Term.Definition.Utils where

import           Data.Functor                     ((<$>))

import           Term.Definition
import           Term.Class
import qualified Term.Telescope                   as Tel
import qualified Term.Context                     as Ctx
import           Term.Var
import           Term.Synonyms
import           Term.Subst
import           Term.TermM
import           Term.Nat

abstractClauseBody
  :: (IsTerm t) => Ctx.ClosedCtx t v -> t v -> Closed (ClauseBody t)
abstractClauseBody ctx0 t0 = go ctx0 (CBNil t0)
  where
    go :: (IsTerm t) => Ctx.ClosedCtx t v -> ClauseBody t v -> Closed (ClauseBody t)
    go Ctx.Empty        body = body
    go (Ctx.Snoc ctx _) body = go ctx (CBArg body)

instantiateClauseBody
  :: (IsTerm t) => ClauseBody t v -> [t v] -> TermM (t v)
instantiateClauseBody (CBNil t) [] =
  return t
instantiateClauseBody (CBArg body) (arg : args) = do
  let f (B _)  = return arg
      f (F v') = var v'
  body' <- subst' body f
  instantiateClauseBody body' args
instantiateClauseBody _ _ =
  error "instantiateClauseBody: wrong number of args"

instance Subst' ClauseBody where
  subst' (CBNil t) f =
    CBNil <$> subst t f
  subst' (CBArg t) f =
    CBArg <$> subst' t (lift' f)
    where
      lift' :: IsTerm t => (Var a -> TermM (t b)) -> Var (Suc a) -> TermM (t (Suc b))
      lift' _  (B n) = var $ B n
      lift' f' (F v) = weaken =<< f' v
