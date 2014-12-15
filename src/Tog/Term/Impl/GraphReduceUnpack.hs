module Tog.Term.Impl.GraphReduceUnpack (GraphReduceUnpack) where

import           Data.IORef                       (IORef, readIORef, writeIORef, newIORef)
import           System.IO.Unsafe                 (unsafePerformIO)

import           Tog.Names
import qualified Tog.Term.Types                   as T
import           Tog.Term.Impl.Common
import           Tog.Prelude

-- Base terms
------------------------------------------------------------------------

newtype GraphReduceUnpack = GRU {unGRU :: IORef Tm}
  deriving (Eq, Typeable)

instance Show GraphReduceUnpack where
  show _ = "<<ref>>"

type Ref = GraphReduceUnpack

data Tm
    = Pi {-# UNPACK #-} !Ref
         {-# UNPACK #-} !Ref
    | Lam {-# UNPACK #-} !Ref
    | Equal {-# UNPACK #-} !Ref
            {-# UNPACK #-} !Ref
            {-# UNPACK #-} !Ref
    | Refl
    | Set
    | Con !(T.Opened QName Ref) ![Ref]
    | App !(T.Head Ref) ![T.Elim Ref]
    deriving (Show, Eq, Typeable)

instance T.Metas GraphReduceUnpack GraphReduceUnpack where
  metas = genericMetas

instance T.Nf GraphReduceUnpack GraphReduceUnpack where
  nf t = do
    t' <- genericNf t
    tView <- liftIO $ readIORef $ unGRU t'
    liftIO $ writeIORef (unGRU t) (tView)
    return t

instance T.PrettyM GraphReduceUnpack GraphReduceUnpack where
  prettyPrecM = genericPrettyPrecM

instance T.ApplySubst GraphReduceUnpack GraphReduceUnpack where
  safeApplySubst = genericSafeApplySubst

instance T.SynEq GraphReduceUnpack GraphReduceUnpack where
  synEq (GRU tRef1) (GRU tRef2) | tRef1 == tRef2 = return True
  synEq t1 t2 = genericSynEq t1 t2

instance T.IsTerm GraphReduceUnpack where
  whnf t = do
    blockedT <- genericWhnf t
    tView <- liftIO . readIORef . unGRU =<< T.ignoreBlocking blockedT
    liftIO $ writeIORef (unGRU t) (tView)
    return $ blockedT

  view ref = do
    t <- liftIO $ readIORef $ unGRU ref
    return $ case t of
      Pi dom cod -> T.Pi dom cod
      Lam body -> T.Lam body
      Equal type_ x y -> T.Equal type_ x y
      Refl -> T.Refl
      Con dataCon args -> T.Con dataCon args
      Set -> T.Set
      App h els -> T.App h els

  unview tView = do
    let t = case tView of
          T.Lam body -> Lam body
          T.Pi dom cod -> Pi dom cod
          T.Equal type_ x y -> Equal type_ x y
          T.Refl -> Refl
          T.Con dataCon args -> Con dataCon args
          T.Set -> Set
          T.App h els -> App h els
    GRU <$> liftIO (newIORef t)

  {-# NOINLINE set #-}
  set = unsafePerformIO $ GRU <$> newIORef Set

  {-# NOINLINE refl #-}
  refl = unsafePerformIO $ GRU <$> newIORef Refl

  {-# NOINLINE typeOfJ #-}
  typeOfJ = unsafePerformIO $ T.runTermM T.sigEmpty genericTypeOfJ

