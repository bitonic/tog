module Term.Impl.GraphReduce (GraphReduce) where

import           Data.IORef                       (IORef, readIORef, writeIORef, newIORef)
import           System.IO.Unsafe                 (unsafePerformIO)

import           Term
import qualified Term.Signature                   as Sig
import           Term.Impl.Common
import           Prelude.Extended

-- Base terms
------------------------------------------------------------------------

newtype GraphReduce = GR {unGR :: IORef (TermView GraphReduce)}
  deriving (Typeable)

instance Show GraphReduce where
  show _ = "<<ref>>"

instance IsTerm GraphReduce where
  termEq (GR tRef1) (GR tRef2) | tRef1 == tRef2 = return True
  termEq t1 t2 = genericTermEq t1 t2

  strengthen = genericStrengthen
  getAbsName' = genericGetAbsName

  whnf t = do
    blockedT <- genericWhnf t
    tView <- liftIO . readIORef . unGR =<< ignoreBlocking blockedT
    liftIO $ writeIORef (unGR t) (tView)
    return $ blockedT

  nf t = do
    t' <- genericNf t
    tView <- liftIO $ readIORef $ unGR t'
    liftIO $ writeIORef (unGR t) (tView)
    return t

  view = liftIO . readIORef . unGR

  unview tView = GR <$> liftIO (newIORef tView)

  set = setGR
  refl = reflGR
  typeOfJ = typeOfJGR

  substs = genericSubsts
  weaken = genericWeaken

{-# NOINLINE setGR #-}
setGR :: GraphReduce
setGR = unsafePerformIO $ GR <$> newIORef Set

{-# NOINLINE reflGR #-}
reflGR :: GraphReduce
reflGR = unsafePerformIO $ GR <$> newIORef Refl

{-# NOINLINE typeOfJGR #-}
typeOfJGR :: GraphReduce
typeOfJGR = unsafePerformIO $ runTermM Sig.empty genericTypeOfJ
