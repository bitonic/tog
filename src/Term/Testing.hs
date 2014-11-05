{-# OPTIONS_GHC -fno-warn-orphans #-}
module Term.Testing where

import           Prelude                          hiding (pi)

import           Prelude.Extended
import           Term                             hiding (lam, pi, equal, set, refl, con, app)
import           Term.Impl
import qualified Term                             as Term
import qualified Term.Signature                   as Sig
import           Syntax
import qualified Syntax.Internal                  as SI

type Tm = Simple

run :: TermM Tm a -> IO a
run = runTermM Sig.empty

tm_ :: (MonadTerm Tm m) => SI.Expr -> m Tm
tm_ = tm B0

tm :: forall m. (MonadTerm Tm m) => Bwd Name -> SI.Expr -> m Tm
tm nms e0 = case e0 of
  SI.Lam n e -> do
    Term.lam =<< tm (nms :< n) e
  SI.Pi n dom cod -> do
    dom' <- tm nms dom
    cod' <- tm (nms :< n) cod
    Term.pi dom' cod'
  SI.Fun dom cod -> do
    join $ Term.pi <$> tm nms dom
                   <*> (weaken_ 1 =<< tm nms cod)
  SI.Equal type_ x y -> do
    join $ Term.equal <$> tm nms type_ <*> tm nms x <*> tm nms y
  SI.Set _ -> do
    return Term.set
  SI.Refl _ -> do
    return Term.refl
  SI.Meta _ -> do
    error "tm.Meta"
  SI.Con dataCon es -> do
    join $ Term.con dataCon <$> mapM (tm nms) es
  SI.App h es -> do
    let h' = case h of
          SI.Var n -> case n `bwdIndex` nms of
                        Nothing -> Def n
                        Just i   -> Var $ mkVar n i
          SI.Def n -> Def n
          SI.J _   -> J
    Term.app h' =<< mapM tmElim es
  where
    tmElim (SI.Proj _)   = error "tm.Proj"
    tmElim (SI.Apply e') = Apply <$> tm nms e'

    bwdIndex y (_  :< x) | y == x = Just 0
    bwdIndex y (xs :< _) = succ <$> bwdIndex y xs
    bwdIndex _ _ = Nothing

-- Abbreviations
------------------------------------------------------------------------

lam :: Name -> SI.Expr -> SI.Expr
lam = SI.Lam

pi :: Name -> SI.Expr -> SI.Expr -> SI.Expr
pi = SI.Pi

(-->) :: SI.Expr -> SI.Expr -> SI.Expr
(-->) = SI.Fun

equal :: SI.Expr -> SI.Expr -> SI.Expr -> SI.Expr
equal = SI.Equal

app :: SI.Head -> [SI.Expr] -> SI.Expr
app h = SI.App h . map SI.Apply

set :: SI.Expr
set = SI.Set SI.noSrcLoc

meta :: Name -> SI.Expr
meta n = SI.App (SI.Def n) []

proj :: Name -> SI.Expr
proj n = SI.App (SI.Def n) []

refl :: SI.Expr
refl = SI.Refl SI.noSrcLoc

con :: Name -> [SI.Expr] -> SI.Expr
con = SI.Con

instance IsString SI.Expr where
  fromString s = SI.App (SI.Var (fromString s)) []

instance IsString SI.Head where
  fromString s = SI.Var (fromString s)
