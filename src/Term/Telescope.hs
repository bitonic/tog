{-# OPTIONS -fno-warn-orphans #-}
module Term.Telescope
    ( -- * 'Tel'
      Tel(..)
    , tel
    , unTel
    , length
    , (++)
    , discharge
    , pi
    ) where

import qualified Prelude
import           Prelude                          hiding (pi, length, lookup, (++))

import qualified Term.Context                     as Ctx
import           Term.Types                       (MonadTerm)
import qualified Term.Types                       as Term
import           Term.Synonyms
import           Term.Substitution                as Sub
import qualified Term.Substitution.Utils          as Term
import           Term.Telescope.Types

-- Tel
------------------------------------------------------------------------

length :: Tel t -> Int
length Empty         = 0
length (Cons _ tel') = 1 + length tel'

-- Instances
----------------------

-- To/from Ctx
--------------

tel :: Ctx.Ctx t -> Tel t
tel ctx0 = go ctx0 Empty
  where
    go Ctx.Empty            tel' = tel'
    go (Ctx.Snoc ctx type_) tel' = go ctx (Cons type_ tel')

unTel :: Tel t -> Ctx.Ctx t
unTel tel0 = go tel0 Ctx.Empty
  where
    go Empty             ctx = ctx
    go (Cons type_ tel') ctx = go tel' (Ctx.Snoc ctx type_)

(++) :: Ctx.Ctx t -> Tel t -> Tel t
Ctx.Empty            ++ tel' = tel'
(Ctx.Snoc ctx type_) ++ tel' = ctx ++ (Cons type_ tel')

-- Methods

instance Term.Subst t (Tel t) where
  applySubst Empty _ = do
    return Empty
  applySubst (Cons (n, type_) tel') rho = do
    type' <- Term.applySubst type_ rho
    tel'' <- Term.applySubst tel' (Sub.lift 1 rho)
    return $ Cons (n, type') tel''

-- | Instantiates an 'Tel' repeatedly until we get to the bottom of
-- it.  Fails If the length of the 'Tel' and the provided list don't
-- match.
discharge :: (Term.IsTerm t, MonadTerm t m) => Tel t -> Term t -> [Term t] -> m t
discharge tel' t args =
  if length tel' == Prelude.length args
  then Term.instantiate t args
  else error "Term.Telescope.discharge"

pi :: (Term.IsTerm t, MonadTerm t m) => Tel (Type t) -> Type t -> m (Type t)
pi = Ctx.pi . unTel
