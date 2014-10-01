module Term.Telescope
    ( -- * 'Tel'
      Tel(..)
    , tel
    , unTel
    , length
    , (++)
    , subst
    , substs
    , instantiate
    , weaken
    , weaken_
    , strengthen
    , strengthen_
    ) where

import qualified Prelude
import           Prelude                          hiding (pi, length, lookup, (++))

import           Control.Monad.Trans.Maybe        (MaybeT(MaybeT), runMaybeT)

import           Prelude.Extended
import           Syntax.Internal                  (Name)
import qualified Term.Context                     as Ctx
import           Term.MonadTerm
import qualified Term.Types                       as Term
import           Term.Synonyms

-- Tel
------------------------------------------------------------------------

-- | A 'Tel' is a list of types, each one ranging over the rest of the
-- list, and with something of at the end -- the inverse of a 'Ctx.Ctx',
-- plus the end element.
data Tel t
    = Empty
    | Cons (Name, t) (Tel (Abs t))
    deriving (Eq, Ord, Typeable)

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

subst :: (Term.IsTerm t, MonadTerm t m) => Int -> t -> Tel t -> m (Tel t)
subst _ _ Empty =
  return Empty
subst ix t (Cons (n, type_) tel') = do
  type' <- Term.subst ix t type_
  t' <- Term.weaken_ 1 t
  tel'' <- subst (ix + 1) t' tel'
  return $ Cons (n, type') tel''

-- | Instantiates an 'Tel' repeatedly until we get to the bottom of
-- it.  Fails If the length of the 'Tel' and the provided list don't
-- match.
substs :: (Term.IsTerm t, MonadTerm t m) => Tel t -> t -> [t] -> m t
substs tel' t args =
  if length tel' == Prelude.length args
  then Term.substs (zip [0..] $ reverse args) t
  else error "Term.Telescope.substs"

-- | Instantiates a bound variable.
instantiate :: (Term.IsTerm t, MonadTerm t m) => Tel t -> t -> m (Tel t)
instantiate tel0 arg = go 0 tel0
  where
    go _ Empty =
      return Empty
    go ix (Cons (n, type_) tel') = do
      arg' <- Term.weaken_ (ix + 1) arg
      type' <- Term.subst ix arg' type_
      Just type'' <- Term.strengthen ix 1 type'
      Cons (n, type'') <$> go (ix + 1) tel'

weaken :: (Term.IsTerm t, MonadTerm t m) => Int -> Int -> Tel t -> m (Tel t)
weaken _ _ Empty =
  return Empty
weaken from by (Cons (n, type_) tel') = do
  type' <- Term.weaken from by type_
  tel'' <- weaken (1 + from) by tel'
  return $ Cons (n, type') tel''

weaken_ :: (Term.IsTerm t, MonadTerm t m) => Int -> Tel t -> m (Tel t)
weaken_ = weaken 0

strengthen :: (Term.IsTerm t, MonadTerm t m) => Int -> Int -> Tel t -> m (Maybe (Tel t))
strengthen _ _ Empty = runMaybeT $ do
  return Empty
strengthen from by (Cons (n, type_) tel') = runMaybeT $ do
  type' <- MaybeT $ Term.strengthen from by type_
  tel'' <- MaybeT $ strengthen (from + 1) by tel'
  return (Cons (n, type') tel'')

strengthen_ :: (Term.IsTerm t, MonadTerm t m) => Int -> Tel t -> m (Maybe (Tel t))
strengthen_ = strengthen 0
