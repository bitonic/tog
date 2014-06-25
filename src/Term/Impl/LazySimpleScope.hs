module Term.Impl.LazySimpleScope (LazySimpleScope) where

import Prelude                                    hiding (pi, abs, foldr)

import           Data.Functor                     ((<$>))
import qualified Data.HashSet                     as HS

import           Bound.Class
import           Bound.Scope.Simple               hiding (instantiate)
import           Prelude.Extras                   (Eq1)
import           Data.Foldable                    (Foldable)
import           Data.Traversable                 (Traversable)
import           Control.Monad                    (ap)
import           Control.Applicative              (Applicative(pure, (<*>)))
import           Data.Typeable                    (Typeable)

import           Syntax.Internal                  (Name)
import           Term
import qualified Term.Signature                   as Sig

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

eliminate' :: LazySimpleScope v -> [Elim LazySimpleScope v] -> LazySimpleScope v
eliminate' (LSS tView) elims = case (tView, elims) of
    (_, []) ->
        LSS tView
    (Con _c args, Proj _ field : es) ->
        if unField field >= length args
        then error "LazySimpleScope.eliminate: Bad elimination"
        else eliminate' (args !! unField field) es
    (Lam body, Apply argument : es) ->
        eliminate' (instantiate body argument) es
    (App h es1, es2) ->
        unview $ App h (es1 ++ es2)
    (_, _) ->
        error $ "Eval.eliminate: Bad elimination"

instance Subst LazySimpleScope where
  var v = LSS $ App (Var v) []

  subst = (>>=)

  substMap = fmap

instance IsTerm LazySimpleScope where
  unview = LSS

  whnfView sig t = unLSS $ ignoreBlocking $ whnf sig t

  whnf = whnf'

whnf' :: Sig.Signature LazySimpleScope -> LazySimpleScope v -> Blocked LazySimpleScope v
whnf' sig t = case unLSS t of
  App (Meta mv) es | Just t' <- Sig.getMetaVarBody sig mv ->
    whnf sig $ eliminate' (substVacuous t') es
  App (Def defName) es | Function _ cs <- Sig.getDefinition sig defName ->
    whnfFun sig defName es $ ignoreInvertible cs
  App J (_ : x : _ : _ : Apply p : Apply refl' : es) ->
    case whnfView sig refl' of
      Refl -> whnf sig $ eliminate' p (x : es)
      _    -> NotBlocked t
  App (Meta mv) elims ->
    MetaVarHead mv elims
  _ ->
    NotBlocked t

whnfFun
  :: Sig.Signature LazySimpleScope
  -> Name -> [Elim LazySimpleScope v] -> [Closed (Clause LazySimpleScope)]
  -> Blocked LazySimpleScope v
whnfFun _ funName es [] =
  NotBlocked $ def funName es
whnfFun sig funName es (Clause patterns body : clauses) =
  case matchClause sig es patterns of
    TTMetaVars mvs ->
      BlockedOn mvs funName es
    TTFail () ->
      whnfFun sig funName es clauses
    TTOK (args0, leftoverEs) -> do
      let args = reverse args0
      let ixArg n = if n >= length args
                    then error "Eval.whnf: too few arguments"
                    else args !! n
      let body' = substInstantiateName ixArg (subst'Vacuous body)
      whnf sig $ eliminate' body' leftoverEs

matchClause
  :: Sig.Signature LazySimpleScope -> [Elim LazySimpleScope v] -> [Pattern]
  -> TermTraverse () ([LazySimpleScope v], [Elim LazySimpleScope v])
matchClause _ es [] =
  pure ([], es)
matchClause sig (Apply arg : es) (VarP : patterns) =
  (\(args, leftoverEs) -> (arg : args, leftoverEs)) <$>
  matchClause sig es patterns
matchClause sig (Apply arg : es) (ConP dataCon dataConPatterns : patterns) = do
  case whnf sig arg of
    MetaVarHead mv _ ->
      TTMetaVars (HS.singleton mv) <*> matchClause sig es patterns
    NotBlocked t | Con dataCon' dataConArgs <- unLSS t ->
      if dataCon == dataCon'
        then matchClause sig (map Apply dataConArgs ++ es) (dataConPatterns ++ patterns)
        else TTFail ()
    _ ->
      TTFail ()
matchClause _ _ _ =
  TTFail ()
