module Term.Telescope
    ( -- * 'Tel'
      Tel(..)
    , ClosedTel
    , tel
    , unTel
    , idTel
    , proxyTel
    , (++)
      -- ** 'Tel' types
    , Proxy(..)
    , Id(..)
    , Prod2(..)
    , ProxyTel
    , ClosedProxyTel
    , IdTel
    , ClosedIdTel
    ) where

import           Prelude                          hiding (pi, length, lookup, (++))

import           Control.Applicative              ((<*>))
import           Data.Functor                     ((<$>))
import           Data.Typeable                    (Typeable)

import           Syntax.Internal                  (Name)
import qualified Term.Context                     as Ctx
import           Term.Subst
import           Term.Var
import           Term.TermM
import           Term.Nat

-- Tel
------------------------------------------------------------------------

-- | A 'Tel' is a list of types, each one ranging over the rest of the
-- list, and with something of at the end -- the inverse of a 'Ctx.Ctx',
-- plus the end element.
data Tel t f v
    = Empty (t f v)
    | Cons (Name, f v) (Tel t f (Suc v))

deriving instance Typeable Tel

type ClosedTel t f = Tel t f Zero

-- Useful types
---------------

-- | A type with no data, useful to create 'Tel's with only types in
-- them.
data Proxy (f :: Nat -> *) (v :: Nat) = Proxy

-- | An identity type, useful to have terms at the end of a 'Tel'.
newtype Id (f :: Nat -> *) v = Id {unId :: f v}

data Prod2 (f :: Nat -> *) v = Prod2 (f v) (f v)

type IdTel    = Tel Id
type ProxyTel = Tel Proxy

type ClosedIdTel t    = IdTel t Zero
type ClosedProxyTel t = ProxyTel t Zero

-- Instances
----------------------

-- To/from Ctx
--------------

tel :: Ctx.Ctx v0 f v -> t f v -> Tel t f v0
tel ctx0 t = go ctx0 (Empty t)
  where
    go :: Ctx.Ctx v0 f v -> Tel t f v -> Tel t f v0
    go Ctx.Empty            tel' = tel'
    go (Ctx.Snoc ctx type_) tel' = go ctx (Cons type_ tel')

idTel :: Ctx.Ctx v0 f v -> f v -> IdTel f v0
idTel ctx t = tel ctx (Id t)

proxyTel :: Ctx.Ctx v0 f v -> ProxyTel f v0
proxyTel ctx = tel ctx Proxy

unTel :: forall t f v0 a.
         Tel t f v0
      -> (forall v. Ctx.Ctx v0 f v -> t f v -> a)
      -> a
unTel tel0 f = go tel0 Ctx.Empty
  where
    go :: Tel t f v -> Ctx.Ctx v0 f v -> a
    go (Empty t)         ctx = f ctx t
    go (Cons type_ tel') ctx = go tel' (Ctx.Snoc ctx type_)

(++) :: Ctx.Ctx v0 f v -> Tel t f v -> Tel t f v0
Ctx.Empty            ++ tel' = tel'
(Ctx.Snoc ctx type_) ++ tel' = ctx ++ (Cons type_ tel')
