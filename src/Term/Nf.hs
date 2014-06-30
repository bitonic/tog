module Term.Nf
    ( nf
    , Nf(nf')
    ) where

import           Prelude                          hiding (pi)

import           Control.Applicative              ((<$>), (<*>))
import           Control.Monad                    ((<=<))

import           Term.Definition
import qualified Term.Signature                   as Sig
import qualified Term.Telescope                   as Tel
import           Term.Class
import           Term.TermM

class Nf t where
  nf' :: (IsTerm f) => Sig.Signature f -> t f v -> TermM (t f v)

instance Nf Elim where
  nf' _   (Proj ix field) = return $ Proj ix field
  nf' sig (Apply t)       = Apply <$> nf sig t

instance (Nf t) => Nf (Tel.Tel t) where
  nf' sig (Tel.Empty t)             = Tel.Empty <$> nf' sig t
  nf' sig (Tel.Cons (n, type_) tel) = Tel.Cons <$> ((n,) <$> nf sig type_) <*> nf' sig tel

instance Nf Tel.Id where
  nf' sig (Tel.Id t) = Tel.Id <$> nf sig t

instance Nf Tel.Proxy where
  nf' _ Tel.Proxy = return Tel.Proxy

instance Nf Clause where
  nf' sig (Clause pats body) =
    Clause pats <$> nf sig body

instance Nf Definition where
  nf' sig (Constant kind t)              = Constant kind <$> nf sig t
  nf' sig (DataCon tyCon type_)          = DataCon tyCon <$> nf' sig type_
  nf' sig (Projection field tyCon type_) = Projection field tyCon <$> nf' sig type_
  nf' sig (Function type_ clauses)       = Function <$> nf sig type_ <*> nfInvertible clauses
    where
      nfInvertible (NotInvertible clauses') =
        NotInvertible <$> mapM (nf' sig) clauses'
      nfInvertible (Invertible injClauses) =
        Invertible <$> mapM (\(th, clause) -> (th ,) <$> nf' sig clause) injClauses

instance Nf TermView where
  nf' sig t = (whnfView sig <=< nf sig <=< unview) t
