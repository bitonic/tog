module TypeCheck3.Check where

import           Term
import {-# SOURCE #-} TypeCheck3.Monad

check
  :: (IsTerm t)
  => Ctx t -> Term t -> Type t -> TC t s ()
