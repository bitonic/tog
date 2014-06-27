module Term.Impl.GraphReduce (GraphReduce) where

import Prelude                                    hiding (pi, abs, foldr)

import           Bound.Var                        (Var(B, F), unvar)
import           Control.Applicative              ((<*>))
import           Control.Monad                    (join)
import           Control.Monad.Trans.Class        (lift)
import           Control.Monad.Trans.Maybe        (MaybeT(MaybeT), runMaybeT)
import           Data.Functor                     ((<$>))
import           Data.IORef                       (IORef, readIORef, writeIORef, newIORef)
import           Data.Typeable                    (Typeable)
import           Data.Traversable                 (traverse)
import           System.IO.Unsafe                 (unsafePerformIO)

import           Term

-- Base terms
------------------------------------------------------------------------

newtype GraphReduce v = GR {unGR :: IORef (TermView GraphReduce v)}
  deriving (Typeable)

instance Subst GraphReduce where
  {-# NOINLINE var #-}
  var v = unview (App (Var v) [])

  subst tRef f = do
    tView <- readIORef $ unGR tRef
    case tView of
      Lam body         -> lam =<< subst body (lift' f)
      Pi dom cod       -> join $ pi <$> subst dom f <*> subst cod (lift' f)
      Equal type_ x y  -> join $ equal <$> subst type_ f <*> subst x f <*> subst y f
      Refl             -> return refl
      Con dataCon args -> join $ con dataCon <$> mapM (`subst` f) args
      Set              -> return set
      App h els  -> do
        els' <- mapM (mapElimM (`subst` f)) els
        case h of
          Var v   -> do t <- f v
                        genericEliminate (readIORef . unGR) t els'
          Def n   -> def n els'
          Meta mv -> app (Meta mv) els'
          J       -> app J els'
    where
      lift' :: Subst t => (a -> TermM (t b)) -> (TermVar a -> TermM (t (TermVar b)))
      lift' _ (B v) = var $ B v
      lift' g (F v) = substMap F =<< g v

instance IsTerm GraphReduce where
  termEq t1Ref t2Ref = do
    t1 <- readIORef $ unGR t1Ref
    t2 <- readIORef $ unGR t2Ref
    termViewEq t1 t2

  strengthen = runMaybeT . go (unvar (const Nothing) Just)
    where
      lift' :: (v -> Maybe v0) -> (TermVar v -> Maybe (TermVar v0))
      lift' _ (B _) = Nothing
      lift' f (F v) = F <$> f v

      go :: (v -> Maybe v0) -> GraphReduce v -> MaybeT TermM (GraphReduce v0)
      go f tRef = do
        tView <- lift $ readIORef $ unGR tRef
        case tView of
          Lam body -> do
            lift . lam =<< go (lift' f) body
          Pi dom cod -> do
            dom' <- go f dom
            cod' <- go (lift' f) cod
            lift $ pi dom' cod'
          Equal type_ x y  -> do
            type' <- go f type_
            x' <- go f x
            y' <- go f y
            lift $ equal type' x' y'
          Refl -> do
            return refl
          Con dataCon args -> do
            lift . con dataCon =<< mapM (go f) args
          Set -> do
            return set
          App h els -> do
            h' <- MaybeT $ return $ traverse f h
            els' <- mapM (mapElimM (go f)) els
            lift $ app h' els'

  getAbsName = genericGetAbsName (readIORef . unGR)

  whnf sig t = do
    blockedT <- termViewGenericWhnf (readIORef . unGR) sig t
    tView <- readIORef . unGR =<< ignoreBlocking blockedT
    writeIORef (unGR t) (tView)
    return $ blockedT

  view = readIORef . unGR

  unview tView = GR <$> newIORef tView

  set = setGR

  refl = reflGR


{-# NOINLINE setGR #-}
setGR :: GraphReduce v
setGR = unsafePerformIO $ GR <$> newIORef Set

{-# NOINLINE reflGR #-}
reflGR :: GraphReduce v
reflGR = unsafePerformIO $ GR <$> newIORef Refl
