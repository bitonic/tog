module Term.Impl.GraphReduce (GraphReduce) where

import           Data.IORef                       (IORef, readIORef, writeIORef, newIORef)
import           System.IO.Unsafe                 (unsafePerformIO)

import           Term.Types
import           Term.Impl.Common
import           TogPrelude

-- Base terms
------------------------------------------------------------------------

newtype GraphReduce = GR {unGR :: IORef (TermView GraphReduce)}
  deriving (Typeable)

instance Show GraphReduce where
  show _ = "<<ref>>"

instance Metas GraphReduce GraphReduce where
  metas = genericMetas

instance Nf GraphReduce GraphReduce where
  nf t = do
    t' <- genericNf t
    tView <- liftIO $ readIORef $ unGR t'
    liftIO $ writeIORef (unGR t) (tView)
    return t

instance PrettyM GraphReduce GraphReduce where
  prettyPrecM = genericPrettyPrecM

instance ApplySubst GraphReduce GraphReduce where
  safeApplySubst = genericSafeApplySubst

instance SynEq GraphReduce GraphReduce where
  synEq (GR tRef1) (GR tRef2) | tRef1 == tRef2 = return True
  synEq t1 t2 = genericSynEq t1 t2

instance IsTerm GraphReduce where
  whnf t = do
    blockedT <- genericWhnf t
    tView <- liftIO . readIORef . unGR =<< ignoreBlocking blockedT
    liftIO $ writeIORef (unGR t) (tView)
    return $ blockedT

  view = liftIO . readIORef . unGR
  unview tView = GR <$> liftIO (newIORef tView)

  {-# NOINLINE set #-}
  set = unsafePerformIO $ GR <$> newIORef Set

  {-# NOINLINE refl #-}
  refl = unsafePerformIO $ GR <$> newIORef Refl

  {-# NOINLINE typeOfJ #-}
  typeOfJ = unsafePerformIO $ runTermM sigEmpty genericTypeOfJ
