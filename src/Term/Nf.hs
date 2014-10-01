module Term.Nf
    ( Nf(nf')
    ) where

import           Prelude                          hiding (pi)

import           Control.Applicative              ((<$>), (<*>))
import           Control.Monad                    ((<=<))

import qualified Term.Signature                   as Sig
import qualified Term.Telescope                   as Tel
import           Term.MonadTerm
import           Term.Types

class Nf t where
  nf' :: (IsTerm f, MonadTerm f m) => t f -> m (t f)

instance Nf Elim where
  nf' (Proj ix field) = return $ Proj ix field
  nf' (Apply t)       = Apply <$> nf t

instance Nf Tel.Tel where
  nf' Tel.Empty                 = return Tel.Empty
  nf' (Tel.Cons (n, type_) tel) = Tel.Cons <$> ((n,) <$> nf type_) <*> nf' tel

instance Nf Clause where
  nf' (Clause pats body) = Clause pats <$> nf body

instance Nf Definition where
  nf'(Constant kind t)                   = Constant kind <$> nf t
  nf'(DataCon tyCon args pars type_)     = DataCon tyCon args <$> nf' pars <*> nf type_
  nf'(Projection field tyCon pars type_) = Projection field tyCon <$> nf' pars <*> nf type_
  nf'(Function type_ clauses)            = Function <$> nf type_ <*> nfInvertible clauses
    where
      nfInvertible (NotInvertible clauses') =
        NotInvertible <$> mapM nf' clauses'
      nfInvertible (Invertible injClauses) =
        Invertible <$> mapM (\(th, clause) -> (th ,) <$> nf' clause) injClauses

instance Nf TermView where
  nf' t = (whnfView <=< nf <=< unview) t
