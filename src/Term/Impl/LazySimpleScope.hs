module Term.Impl.LazySimpleScope (LazySimpleScope) where

import Prelude                                    hiding (pi, abs, foldr)

import           Bound.Var                        (Var(B, F))
import           Bound.Class
import           Bound.Scope.Simple               hiding (instantiate)
import           Prelude.Extras                   (Eq1)
import           Data.Foldable                    (Foldable)
import           Data.Functor                     ((<$>))
import           Data.Traversable                 (Traversable, traverse)
import           Control.Monad                    (ap, join)
import           Control.Applicative              (Applicative(pure, (<*>)))
import           Data.Typeable                    (Typeable)

import           Term

-- Base terms
------------------------------------------------------------------------

newtype LazySimpleScope v = LSS {unLSS :: TermView LazySimpleScope v}
    deriving (Eq, Eq1, Functor, Foldable, Traversable, Typeable)

instance Applicative LazySimpleScope where
    pure = return
    (<*>) = ap

instance Monad LazySimpleScope where
    return v = LSS (App (Var v) [])

    LSS term0 >>= f = LSS $ case term0 of
        Lam body           -> Lam (unscope (Scope body >>>= f))
        Pi domain codomain -> Pi (domain >>= f) (unscope (Scope codomain >>>= f))
        Equal type_ x y    -> Equal (type_ >>= f) (x >>= f) (y >>= f)
        Set                -> Set
        Con n elims        -> Con n (map (>>= f) elims)
        Refl               -> Refl
        App h elims        ->
            let elims' = map (>>>= f) elims
            in case h of
                   Var v   -> unLSS $ eliminate' (f v) elims'
                   Def n   -> App (Def n)   elims'
                   J       -> App J         elims'
                   Meta mv -> App (Meta mv) elims'

instantiate' :: Abs LazySimpleScope v -> LazySimpleScope v -> LazySimpleScope v
instantiate' abs' t = abs' >>= \v -> case v of
  B _  -> t
  F v' -> return v'

eliminate' :: LazySimpleScope v -> [Elim LazySimpleScope v] -> LazySimpleScope v
eliminate' (LSS tView) elims = case (tView, elims) of
    (_, []) ->
        LSS tView
    (Con _c args, Proj _ field : es) ->
        if unField field >= length args
        then error "LazySimpleScope.eliminate: Bad elimination"
        else eliminate' (args !! unField field) es
    (Lam body, Apply argument : es) ->
        eliminate' (instantiate' body argument) es
    (App h es1, es2) ->
        LSS $ App h (es1 ++ es2)
    (_, _) ->
        error $ "Eval.eliminate: Bad elimination"

instance Subst LazySimpleScope where
  var = return . return

  subst t f = join <$> traverse f t

  substMap f t = return $ fmap f t

instance IsTerm LazySimpleScope where
  unview = return . LSS
  view  = return . unLSS

  set  = LSS Set
  refl = LSS Refl
