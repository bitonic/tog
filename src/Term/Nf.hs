module Term.Nf
    ( Nf(nf')
    ) where

import           Prelude                          hiding (pi)

import           Control.Applicative              ((<$>), (<*>))
import           Control.Monad                    ((<=<))

import qualified Term.Signature                   as Sig
import qualified Term.Telescope                   as Tel
import           Term.TermM
import           Term.Class

class Nf t where
  nf' :: (IsTerm f) => Sig.Signature f -> t f -> TermM (t f)

instance Nf Elim where
  nf' _   (Proj ix field) = return $ Proj ix field
  nf' sig (Apply t)       = Apply <$> nf sig t

instance Nf Tel.Tel where
  nf' _   Tel.Empty                 = return Tel.Empty
  nf' sig (Tel.Cons (n, type_) tel) = Tel.Cons <$> ((n,) <$> nf sig type_) <*> nf' sig tel

instance Nf Clause where
  nf' sig (Clause pats body) =
    Clause pats <$> nf sig body

instance Nf Definition where
  nf' sig (Constant kind t)                   = Constant kind <$> nf sig t
  nf' sig (DataCon tyCon pars type_)          = DataCon tyCon <$> nf' sig pars <*> nf sig type_
  nf' sig (Projection field tyCon pars type_) = Projection field tyCon <$> nf' sig pars <*> nf sig type_
  nf' sig (Function type_ clauses)            = Function <$> nf sig type_ <*> nfInvertible clauses
    where
      nfInvertible (NotInvertible clauses') =
        NotInvertible <$> mapM (nf' sig) clauses'
      nfInvertible (Invertible injClauses) =
        Invertible <$> mapM (\(th, clause) -> (th ,) <$> nf' sig clause) injClauses

instance Nf TermView where
  nf' sig t = (whnfView sig <=< nf sig <=< unview) t
