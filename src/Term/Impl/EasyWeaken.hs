module Term.Impl.EasyWeaken where

import           Bound                            (Var(F, B))
import           Data.Functor                     ((<$>))
import           Data.IORef                       (IORef, readIORef, writeIORef, newIORef)
import           Data.Typeable                    (Typeable)
import           System.IO.Unsafe                 (unsafePerformIO)

import           Term
import           Term.Impl.Common

newtype EasyWeaken v = EW {unEW :: IORef (EasyWeaken' v)}
  deriving (Typeable)

data EasyWeaken' v where
  Normal   :: TermView EasyWeaken v -> EasyWeaken' v
  Weakened :: EasyWeaken v -> EasyWeaken' (TermVar v)
  deriving (Typeable)

-- toTerm :: (IsTerm t) => EasyWeaken v -> TermM (t v)
-- toTerm (EW ewRef) = do
--   ew <- readIORef ewRef
--   t <- case ew of
--     Weakened ew -> do
--       t <- toTerm ew
--       t' <- weaken t
--       writeIORef ewRef $ Normal t'
--       return t'
--     Normal t -> do
--       return t
--   return t

instance Subst EasyWeaken where
  var v = unview (App (Var v) [])
  subst ew f = genericSubst ew f

-- viewEasyWeaken' :: EasyWeaken' v -> TermM (TermView EasyWeaken v)

instance IsTerm EasyWeaken where
  weaken ew = do
    EW <$> newIORef (Weakened ew)

  termEq (EW ewRef1) (EW ewRef2) | ewRef1 == ewRef2 = do
    return True
  -- TODO here we could avoid weakening if both are Weakened, but we
  -- trip over Eq constraints...
  termEq ew1 ew2 = genericTermEq ew1 ew2
    -- ew1' <- readIORef ewRef2
    -- ew2' <- readIORef ewRef2
    -- go ew1' ew2'
    -- where
    --   go :: Eq v => EasyWeaken' v -> EasyWeaken' v -> TermM Bool
    --   go (Weakened ew1) (Weakened ew2) = go ew1 ew2
    --   go (Normal t1)    (Normal t2)    = genericTermViewEq t1 t2
    --   go (Normal t1)    t2             = genericTermViewEq t1 =<< viewEasyWeaken' t2
    --   go t1             (Normal t2)    = genericTermViewEq t2 =<< viewEasyWeaken' t1

  strengthen (EW ewRef) = do
    ew <- readIORef ewRef
    case ew of
      Weakened ew' -> return $ Just ew'
      Normal _     -> genericStrengthen (EW ewRef)

  -- TODO write faster versions
  getAbsName' = genericGetAbsName

  whnf sig t = do
    blockedT <- genericWhnf sig t
    ew <- readIORef . unEW =<< ignoreBlocking blockedT
    writeIORef (unEW t) ew
    return $ blockedT

  nf sig t = do
    t' <- genericNf sig t
    ew <- readIORef $ unEW t'
    writeIORef (unEW t) ew
    return t

  view (EW ewRef) = do
    ew <- readIORef ewRef
    ewView <- case ew of
      Normal t    -> return t
      Weakened ew' -> do
        ewView <- view ew'
        -- TODO can we mutate this in place?
        view =<< genericSubstView ewView (var . F)
    writeIORef ewRef (Normal ewView)
    return ewView

  unview tView = EW <$> newIORef (Normal tView)

  set = setEW
  refl = reflEW
  typeOfJ = typeOfJEW

{-# NOINLINE setEW #-}
setEW :: EasyWeaken v
setEW = unsafePerformIO $ unview Set

{-# NOINLINE reflEW #-}
reflEW :: EasyWeaken v
reflEW = unsafePerformIO $ unview Refl

{-# NOINLINE typeOfJEW #-}
typeOfJEW :: Closed EasyWeaken
typeOfJEW = unsafePerformIO genericTypeOfJ
