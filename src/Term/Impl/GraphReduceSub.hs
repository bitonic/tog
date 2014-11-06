module Term.Impl.GraphReduceSub where

import           Data.IORef                       (IORef, readIORef, writeIORef, newIORef)
import           System.IO.Unsafe                 (unsafePerformIO)

import qualified PrettyPrint                      as PP
import           Syntax
import           Term
import qualified Term.Signature                   as Sig
import qualified Term.Substitution.Types          as Sub
import qualified Term.Substitution                as Sub
import           Term.Impl.Common
import           Prelude.Extended

data NoSub

data GRS a where
  Pi :: !Ref -> GRS NoSub
{-
data GraphReduceSub = GRS !(Substitution GraphReduceSub)
                          {-# UNPACK #-} !(IORef Tm)
  deriving (Eq, Typeable)

instance Show GraphReduceSub where
  show _ = "<<GRS>>"

type Tm = TermView GraphReduceSub

instance MetaVars GraphReduceSub GraphReduceSub where
  metaVars = genericMetaVars

instance Nf GraphReduceSub GraphReduceSub where
  nf = genericNf

instance PrettyM GraphReduceSub GraphReduceSub where
  prettyPrecM = genericPrettyPrecM

instance Subst GraphReduceSub GraphReduceSub where
  applySubst (GRS rho t) sgm = do
    rho' <- Sub.compose sgm rho
    return $ GRS rho' t

instance SynEq GraphReduceSub GraphReduceSub where
  synEq x y = return (x == y)

instance IsTerm GraphReduceSub where
  whnf (GRS rho t) = do
    blockedT <- genericWhnf t
    GRS rho' tView <- ignoreBlocking blockedT
    

  view (GRS rho t) = (`applySubst'` rho) =<< liftIO (readIORef t)
  unview tView = GRS Sub.id <$> liftIO (newIORef tView)

  {-# NOINLINE set #-}
  set = unsafePerformIO $ GRS Sub.id <$> newIORef Set

  {-# NOINLINE refl #-}
  refl = unsafePerformIO $ GRS Sub.id <$> newIORef Refl

  {-# NOINLINE typeOfJ #-}
  typeOfJ = unsafePerformIO $ runTermM Sig.empty genericTypeOfJ

  canStrengthen = genericCanStrengthen

applySubst'
  :: (MonadTerm GraphReduceSub m) => TermView GraphReduceSub -> Substitution GraphReduceSub -> m (TermView GraphReduceSub)
applySubst' t Sub.Id = do
  return t
applySubst' tView rho = do
  case tView of
    Lam body ->
      Lam <$> applySubst body (Sub.lift 1 rho)
    Pi dom cod ->
      Pi <$> applySubst dom rho <*> applySubst cod (Sub.lift 1 rho)
    Equal type_ x y  ->
      Equal <$> applySubst type_ rho
            <*> applySubst x rho
            <*> applySubst y rho
    Refl ->
      return Refl
    Con dataCon args ->
      Con dataCon <$> applySubst args rho
    Set ->
      return Set
    App h els  -> do
      els' <- applySubst els rho
      case h of
        Var v   -> do GRS sgm tView' <- (`eliminate` els') =<< Sub.lookup v rho
                      (`applySubst'` sgm) =<< liftIO (readIORef tView')
        Def n   -> return $ App (Def n) els'
        Meta mv -> return $ App (Meta mv) els'
        J       -> return $ App J els'

-- instance IsTerm Tm where
-}

{-
type Tm = GraphReduceSub

data GraphReduceSub
  = Pi  !Tm
        !Tm
  | Lam  !Tm
  | Equal  !Tm
           !Tm
           !Tm
  | Refl
  | Set
  | Con !Name ![Tm]
  | App T.Head ![T.Elim Tm]
  | Sub !(T.Substitution Tm)  !Tm
  deriving (Show, Read, Eq, Typeable)

instance T.MetaVars GraphReduceSub GraphReduceSub where
  metaVars = genericMetaVars

instance T.Nf GraphReduceSub GraphReduceSub where
  nf = genericNf

instance T.PrettyM GraphReduceSub GraphReduceSub where
  prettyPrecM = genericPrettyPrecM

instance T.Subst GraphReduceSub GraphReduceSub where
  {-# NOINLINE applySubst #-}
  applySubst t Sub.Id = do
    return t
  applySubst t sub = do
    case t of
      Sub sub' ref' -> do
        sub'' <- Sub.compose sub sub'
        T.applySubst ref' sub''
      App (T.Var v) [] -> do
        genericApplySubst t sub
      _ -> do
       return $ Sub sub t

instance T.SynEq GraphReduceSub GraphReduceSub where
  synEq t1 t2 = genericSynEq t1 t2

instance T.IsTerm GraphReduceSub where
  whnf = genericWhnf

  view t = do
    case t of
      Sub sub t' -> do
        view =<< genericApplySubst t' sub
      Pi dom cod -> do
        return $ T.Pi dom cod
      Lam body -> do
        return $ T.Lam body
      Equal type_ x y -> do
        return $ T.Equal type_ x y
      Refl -> do
        return $ T.Refl
      Con dataCon args -> do
        return $ T.Con dataCon args
      Set -> do
        return T.Set
      App h els -> do
        return $ T.App h els

  unview tView = do
    let t = case tView of
          T.Lam body -> Lam body
          T.Pi dom cod -> Pi dom cod
          T.Equal type_ x y -> Equal type_ x y
          T.Refl -> Refl
          T.Con dataCon args -> Con dataCon args
          T.Set -> Set
          T.App h els -> App h els
    return t

  set = setGRS
  refl = reflGRS
  typeOfJ = typeOfJGRS

  canStrengthen = genericCanStrengthen

{-# NOINLINE setGRS #-}
setGRS :: GraphReduceSub
setGRS = Set

{-# NOINLINE reflGRS #-}
reflGRS :: GraphReduceSub
reflGRS = Refl

{-# NOINLINE typeOfJGRS #-}
typeOfJGRS :: GraphReduceSub
typeOfJGRS = unsafePerformIO $ T.runTermM Sig.empty genericTypeOfJ
-}


{-
-- Base terms
------------------------------------------------------------------------

newtype GraphReduceSub = GRS {unGRS :: IORef Tm}
  deriving (Eq, Typeable)

instance Show GraphReduceSub where
  show _ = "<<ref>>"

type Ref = GraphReduceSub

data Tm
  = Pi {-# UNPACK #-} !Ref
       {-# UNPACK #-} !Ref
  | Lam {-# UNPACK #-} !Ref
  | Equal {-# UNPACK #-} !Ref
          {-# UNPACK #-} !Ref
          {-# UNPACK #-} !Ref
  | Refl
  | Set
  | Con !Name ![Ref]
  | App T.Head ![T.Elim Ref]
  | Sub !(T.Substitution Ref) {-# UNPACK #-} !Ref
  deriving (Show, Eq, Typeable)

instance T.MetaVars GraphReduceSub GraphReduceSub where
  metaVars = genericMetaVars

instance T.Nf GraphReduceSub GraphReduceSub where
  nf t = do
    t' <- genericNf t
    tView <- liftIO $ readIORef $ unGRS t'
    liftIO $ writeIORef (unGRS t) (tView)
    return t

instance T.PrettyM GraphReduceSub GraphReduceSub where
  prettyPrecM = genericPrettyPrecM

instance T.Subst GraphReduceSub GraphReduceSub where
  applySubst ref Sub.Id = do
    return ref
  applySubst ref sub = do
    t <- liftIO $ readIORef $ unGRS ref
    case t of
      Sub sub' ref' -> do
        sub'' <- Sub.compose sub sub'
        T.applySubst ref' sub''
      _ -> do
       GRS <$> liftIO (newIORef (Sub sub ref))

instance T.SynEq GraphReduceSub GraphReduceSub where
  synEq (GRS tRef1) (GRS tRef2) | tRef1 == tRef2 = return True
  synEq t1 t2 = genericSynEq t1 t2

instance T.IsTerm GraphReduceSub where
  whnf t = do
    blockedT <- genericWhnf t
    tView <- liftIO . readIORef . unGRS =<< T.ignoreBlocking blockedT
    liftIO $ writeIORef (unGRS t) (tView)
    return $ blockedT

  view ref = do
    t <- liftIO $ readIORef $ unGRS ref
    case t of
      Sub sub ref' -> do
        view =<< genericApplySubst ref' sub
      Pi dom cod -> do
        return $ T.Pi dom cod
      Lam body -> do
        return $ T.Lam body
      Equal type_ x y -> do
        return $ T.Equal type_ x y
      Refl -> do
        return $ T.Refl
      Con dataCon args -> do
        return $ T.Con dataCon args
      Set -> do
        return T.Set
      App h els -> do
        return $ T.App h els

  unview tView = do
    let t = case tView of
          T.Lam body -> Lam body
          T.Pi dom cod -> Pi dom cod
          T.Equal type_ x y -> Equal type_ x y
          T.Refl -> Refl
          T.Con dataCon args -> Con dataCon args
          T.Set -> Set
          T.App h els -> App h els
    GRS <$> liftIO (newIORef t)

  set = setGRS
  refl = reflGRS
  typeOfJ = typeOfJGRS

  canStrengthen = genericCanStrengthen

-- genericApplySubst
--   :: (IsTerm t, MonadTerm t m) => t -> Substitution t -> m t
-- genericApplySubst t Sub.Id = do
--   return t
-- genericApplySubst t rho = do
--   tView <- whnfView t
--   case tView of
--     Lam body ->
--       lam =<< applySubst body (Sub.lift 1 rho)
--     Pi dom cod ->
--       join $ pi <$> applySubst dom rho <*> applySubst cod (Sub.lift 1 rho)
--     Equal type_ x y  ->
--       join $ equal <$> applySubst type_ rho
--                    <*> applySubst x rho
--                    <*> applySubst y rho
--     Refl ->
--       return refl
--     Con dataCon args ->
--       join $ con dataCon <$> applySubst args rho
--     Set ->
--       return set
--     App h els  -> do
--       els' <- applySubst els rho
--       case h of
--         Var v   -> (`eliminate` els') =<< Sub.lookup v rho
--         Def n   -> app (Def n) els'
--         Meta mv -> app (Meta mv) els'
--         J       -> app J els'

-- applySubst :: (T.MonadTerm Ref m) => Ref -> T.Substitution Ref -> m Ref
-- applySubst ref Sub.Id = do
--   return ref
-- applySubst ref rho = do
--   tView <- liftIO $ readIORef $ unGRS $ ref
--   case tView of
--     Lam body ->
--       T.lam =<< T.applySubst body (Sub.lift 1 rho)
--     Pi dom cod ->
--       join $ T.pi <$> T.applySubst dom rho <*> T.applySubst cod (Sub.lift 1 rho)
--     Equal type_ x y  ->
--       join $ T.equal <$> T.applySubst type_ rho
--                      <*> T.applySubst x rho
--                      <*> T.applySubst y rho
--     Refl ->
--       return T.refl
--     Con dataCon args ->
--       join $ T.con dataCon <$> T.applySubst args rho
--     Set ->
--       return T.set
--     App h els  -> do
--       els' <- T.applySubst els rho
--       case h of
--         T.Var v   -> (`T.eliminate` els') =<< Sub.lookup v rho
--         T.Def n   -> T.app (T.Def n) els'
--         T.Meta mv -> T.app (T.Meta mv) els'
--         T.J       -> T.app T.J els'

{-# NOINLINE setGRS #-}
setGRS :: GraphReduceSub
setGRS = unsafePerformIO $ GRS <$> newIORef Set

{-# NOINLINE reflGRS #-}
reflGRS :: GraphReduceSub
reflGRS = unsafePerformIO $ GRS <$> newIORef Refl

{-# NOINLINE typeOfJGRS #-}
typeOfJGRS :: GraphReduceSub
typeOfJGRS = unsafePerformIO $ T.runTermM Sig.empty genericTypeOfJ
-}
