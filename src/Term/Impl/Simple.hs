module Term.Impl.Simple (Simple) where

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

newtype Simple v = S {unS :: TermView Simple v}
    deriving (Eq, Eq1, Functor, Foldable, Traversable, Typeable)

instance Applicative Simple where
    pure = return
    (<*>) = ap

instance Monad Simple where
    return v = S (App (Var v) [])

    S term0 >>= f = S $ case term0 of
        Lam body           -> Lam (unscope (Scope body >>>= f))
        Pi domain codomain -> Pi (domain >>= f) (unscope (Scope codomain >>>= f))
        Equal type_ x y    -> Equal (type_ >>= f) (x >>= f) (y >>= f)
        Set                -> Set
        Con n elims        -> Con n (map (>>= f) elims)
        Refl               -> Refl
        App h elims        ->
            let elims' = map (>>>= f) elims
            in case h of
                   Var v   -> unS $ eliminate' (f v) elims'
                   Def n   -> App (Def n)   elims'
                   J       -> App J         elims'
                   Meta mv -> App (Meta mv) elims'

instantiate' :: Abs Simple v -> Simple v -> Simple v
instantiate' abs' t = abs' >>= \v -> case v of
  B _  -> t
  F v' -> return v'

eliminate' :: Simple v -> [Elim Simple v] -> Simple v
eliminate' (S tView) elims = case (tView, elims) of
    (_, []) ->
        S tView
    (Con _c args, Proj _ field : es) ->
        if unField field >= length args
        then error "Simple.eliminate: Bad elimination"
        else eliminate' (args !! unField field) es
    (Lam body, Apply argument : es) ->
        eliminate' (instantiate' body argument) es
    (App h es1, es2) ->
        S $ App h (es1 ++ es2)
    (_, _) ->
        error $ "Eval.eliminate: Bad elimination"

instance Subst Simple where
  var = return . return

  subst t f = join <$> traverse f t

  substMap f t = return $ fmap f t

instance IsTerm Simple where
  unview = return . S
  view  = return . unS

  set  = S Set
  refl = S Refl
