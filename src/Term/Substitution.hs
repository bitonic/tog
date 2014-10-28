{-# LANGUAGE OverloadedStrings #-}
module Term.Substitution
  ( -- * Type
    Substitution
  , id
  , weaken
  , snoc
  , strengthen
  , lift
    -- * Operations
  , compose
  , lookup
  ) where

import           Prelude                          hiding (pi, length, lookup, (++), drop, id)

import           Prelude.Extended                 hiding (lift)
import           Term.Substitution.Types
import           Term.Synonyms
import           Term.Types

-- Smart constructors
------------------------------------------------------------------------

id :: Substitution t
id = Id

weaken :: Int -> Substitution t -> Substitution t
weaken 0 rho            = rho
weaken n (Weaken m rho)     = Weaken (n + m) rho
weaken n (Strengthen m rho) = case n - m of
                                0         -> rho
                                k | k > 0 -> Weaken k rho
                                k         -> Strengthen k rho
weaken n rho                = Weaken n rho

strengthen :: Int -> Substitution t -> Substitution t
strengthen 0 rho                = rho
strengthen n (Strengthen m rho) = Strengthen (m + n) rho
strengthen n (Weaken m rho)     = case n - m of
                                    0         -> rho
                                    k | k < 0 -> Strengthen k rho
                                    k         -> Weaken k rho
strengthen n rho                = Strengthen n rho

-- TODO here we could pattern match on the term and optimize away -- see
-- Agda.TypeChecking.Substitute
snoc :: Substitution t -> Term t -> Substitution t
snoc = Snoc

lift :: Int -> Substitution t -> Substitution t
lift 0 rho          = rho
lift _ Id           = Id
lift k (Lift n rho) = Lift (n + k) rho
lift k rho          = Lift k rho

-- Operations
------------------------------------------------------------------------

drop :: Int -> Substitution t -> Substitution t
drop n rho                | n <= 0 = rho
drop n Id                 = weaken n id
drop n (Weaken m rho)     = weaken m (drop n rho)
drop n (Snoc rho _)       = drop (n - 1) rho
drop n (Strengthen m rho) = drop (n - m) rho
drop _ (Lift 0 _)         = error "drop.Lift"
drop n (Lift m rho)       = weaken 1 $ drop (n - 1) $ lift (m - 1) rho

compose
  :: (IsTerm t, MonadTerm t m)
  => Substitution t -> Substitution t -> m (Substitution t)
compose rho Id =
  return rho
compose Id  rho =
  return rho
compose rho (Weaken n sgm) =
  compose (drop n rho) sgm
compose rho (Snoc sgm u) =
  Snoc <$> compose rho sgm <*> applySubst rho u
compose rho (Strengthen n sgm) =
  Strengthen n <$> compose rho sgm
compose _ (Lift 0 _) =
  error "compose.Lift 0"
compose (Snoc rho u) (Lift n sgm) =
  Snoc <$> compose rho (lift (n - 1) sgm) <*> return u
compose rho (Lift n sgm) =
  Snoc <$> compose rho (weaken 1 (lift (n - 1) sgm))
       <*> lookup (boundVar "_") rho

lookup :: (IsTerm t, MonadTerm t m) => Var -> Substitution t -> m (Term t)
lookup v0 rho0 = go rho0 (varIndex v0)
  where
    nm = varName v0

    go rho i = case rho of
      Id                -> do var v
      Weaken n Id       -> do let j = i + n
                              let _assert@True = j >= 0
                              var $ V $ named nm j
      Weaken n rho'     -> do applySubst (weaken n id) =<< go rho' i
      Snoc rho' u       -> do let _assert@True = i >= 0
                              if i == 0 then return u else go rho' (i - 1)
      Strengthen n rho' -> do let _assert@True = n >= 0
                              let _assert@True = i >= n
                              go rho' (i - n)
      Lift n rho'       -> do if i < n
                                then var v
                                else applySubst (weaken n id) =<< go rho' (i - n)
      where
        v = V $ named nm i
