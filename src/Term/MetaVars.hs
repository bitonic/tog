module Term.MetaVars
  ( MetaVars(metaVars')
  ) where

import qualified Data.HashSet                     as HS

import           Term.MonadTerm
import qualified Term.Telescope                   as Tel
import qualified Term.Signature                   as Sig
import           Term.Types
import           Prelude.Extended

class MetaVars t where
  metaVars' :: (IsTerm f, MonadTerm f m) => t f -> m (HS.HashSet MetaVar)

instance MetaVars Elim where
  metaVars' (Proj ix field) = return mempty
  metaVars' (Apply t)       = metaVars t

instance MetaVars Tel.Tel where
  metaVars' Tel.Empty                 = return mempty
  metaVars' (Tel.Cons (_, type_) tel) = (<>) <$> metaVars type_ <*> metaVars' tel

instance MetaVars Clause where
  metaVars' (Clause _ body) = metaVars body

instance MetaVars Definition where
  metaVars' (Constant _ t)              = metaVars t
  metaVars' (DataCon _ _ pars type_)    = (<>) <$> metaVars' pars <*> metaVars type_
  metaVars' (Projection _ _ pars type_) = (<>) <$> metaVars' pars <*> metaVars type_
  metaVars' (Function type_ clauses)    = (<>) <$> metaVars type_ <*> metaVarsInvertible clauses
    where
      metaVarsInvertible (NotInvertible clauses') =
        mconcat <$> mapM metaVars' clauses'
      metaVarsInvertible (Invertible injClauses) =
        mconcat <$> mapM (metaVars' . snd) injClauses

instance MetaVars TermView where
  metaVars' t = (metaVars <=< unview) t

instance MetaVars Sig.Signature where
  metaVars' sig = do
    mconcat <$> mapM (metaVars' . Sig.getDefinition sig) (Sig.definedNames sig)
