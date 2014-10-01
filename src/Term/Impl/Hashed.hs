module Term.Impl.Hashed where

import qualified Data.HashTable.IO                as HT
import           System.IO.Unsafe                 (unsafePerformIO)

import           Term
import qualified Term.Signature                   as Sig
import           Term.Impl.Common
import           Prelude.Extended


data Hashed = H Int (TermView Hashed)
  deriving (Typeable, Show)

instance Eq Hashed where
  H i1 t1 == H i2 t2 = i1 == i2 && t1 == t2

instance Hashable Hashed where
  hashWithSalt s (H i _) = s `hashWithSalt` i

instance IsTerm Hashed where
  strengthen = genericStrengthen
  getAbsName' = genericGetAbsName

  whnf t = do
    t' <- fromMaybe t <$> liftIO (lookupWhnfTerm t)
    blockedT <- genericWhnf t'
    -- TODO don't do a full traversal for this check
    t'' <- ignoreBlocking blockedT
    unless (t == t'') $ liftIO $ do
      -- TODO do not add both if we didn't get anything the with
      -- `lookupWhnfTerm'.
      insertWhnfTerm t t''
      insertWhnfTerm t' t''
    return blockedT
  nf = genericNf

  view (H _ t) = return t
  unview tv = return $ H (hash tv) tv

  substs = genericSubsts
  weaken = genericWeaken

  set = H (hash (Set :: Closed (TermView Hashed))) Set
  refl = H (hash (Refl :: Closed (TermView Hashed))) Refl

  typeOfJ = typeOfJH

{-# NOINLINE typeOfJH #-}
typeOfJH :: Closed Hashed
typeOfJH = unsafePerformIO $ monadTermIO Sig.empty genericTypeOfJ

-- Table

type TableKey = Hashed

{-# NOINLINE hashedTable #-}
hashedTable :: HT.CuckooHashTable TableKey Hashed
hashedTable = unsafePerformIO HT.new

lookupWhnfTerm :: Hashed -> IO (Maybe Hashed)
lookupWhnfTerm t0 = do
  HT.lookup hashedTable t0

insertWhnfTerm :: Hashed -> Hashed -> IO ()
insertWhnfTerm t1 t2 = HT.insert hashedTable t1 t2
