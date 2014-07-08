module Term.Impl.Hashed where

import           Control.Monad                    (unless)
import           Data.Dynamic                     (Dynamic, fromDynamic, toDyn)
import           Data.Functor                     ((<$>))
import qualified Data.HashTable.IO                as HT
import           Data.Hashable                    (Hashable, hashWithSalt, hash)
import           Data.Maybe                       (fromMaybe)
import           Data.Typeable                    (Typeable, cast)
import           Prelude.Extras                   (Eq1((==#)))
import           System.IO.Unsafe                 (unsafePerformIO)

import           Term
import           Term.Impl.Common


data Hashed v = H Int (TermView Hashed v)
  deriving (Typeable)

instance Eq (Hashed v) where
  H i1 t1 == H i2 t2 = i1 == i2 && go t1 t2
    where
      go (Lam body1) (Lam body2) =
        body1 == body2

instance Hashable (Hashed v) where
  hashWithSalt s (H i _) = s `hashWithSalt` i

instance Subst Hashed where
  var v = unview (App (Var v) [])

  subst = genericSubst

instance IsTerm Hashed where
  termEq t1@(H i1 _) t2@(H i2 _) =
    if i1 == i2 then genericTermEq t1 t2 else return False

  strengthen = genericStrengthen
  getAbsName = genericGetAbsName

  whnf sig t = do
    t' <- fromMaybe t <$> lookupWhnfTerm t
    blockedT <- genericWhnf sig t'
    -- TODO don't do a full traversal for this check
    t'' <- ignoreBlocking blockedT
    unless (t == t'') $ do
      -- TODO do not add both if we didn't get anything the with
      -- `lookupWhnfTerm'.
      insertWhnfTerm t t''
      insertWhnfTerm t' t''
    return blockedT
  nf = genericNf

  view (H _ t) = return t
  unview tv = return $ H (hash tv) tv

  set = H (hash (Set :: Closed (TermView Hashed))) Set
  refl = H (hash (Refl :: Closed (TermView Hashed))) Refl

  typeOfJ = typeOfJH

{-# NOINLINE typeOfJH #-}
typeOfJH :: Closed Hashed
typeOfJH = unsafePerformIO genericTypeOfJ

-- Table

data TableKey = forall v. TableKey (Hashed v)

instance Hashable TableKey where
  hashWithSalt s (TableKey t) = s `hashWithSalt` t

instance Eq TableKey where
  TableKey t1 == TableKey t2 = case (cast t2) of
    Just t2' -> t1 == t2'
    _        -> False

{-# NOINLINE hashedTable #-}
hashedTable :: HT.CuckooHashTable TableKey Dynamic
hashedTable = unsafePerformIO HT.new

lookupWhnfTerm :: Hashed v -> IO (Maybe (Hashed v))
lookupWhnfTerm t0 = do
  mbT <- HT.lookup hashedTable (TableKey t0)
  case mbT of
    Nothing -> return Nothing
    Just t1 -> case fromDynamic t1 of
      Just t2 -> return t2
      Nothing -> error "impossible.lookupWhnfTerm"

insertWhnfTerm :: Hashed v -> Hashed v -> IO ()
insertWhnfTerm t1 t2 = HT.insert hashedTable (TableKey t1) (toDyn t2)

