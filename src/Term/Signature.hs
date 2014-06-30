module Term.Signature
    ( Signature
    , empty
      -- * Definitions
    , getDefinition
    , addDefinition
    , definedNames
      -- * MetaVars
    , getMetaVarType
    , getMetaVarBody
    , addMetaVar
    , instantiateMetaVar
    , metaVarsTypes
    , metaVarsBodies
    ) where

import qualified Data.HashMap.Strict              as HMS
import           Data.Void                        (Void)

import           Syntax.Internal                  (Name)
import           Term.Definition
import           Text.PrettyPrint.Extended        (render)
import           Term.MetaVar

-- | A 'Signature' stores every globally scoped thing.  That is,
-- 'Definition's and 'MetaVar's bodies and types.
data Signature t = Signature
    { sDefinitions :: HMS.HashMap Name (Closed (Definition t))
    , sMetasTypes  :: HMS.HashMap MetaVar (Closed (Type t))
    , sMetasBodies :: HMS.HashMap MetaVar (Closed (Term t))
    -- ^ INVARIANT: Every 'MetaVar' in 'sMetaBodies' is also in
    -- 'sMetasTypes'.
    , sMetasCount  :: Int
    }

empty :: Signature t
empty = Signature HMS.empty HMS.empty HMS.empty 0

-- | Gets a definition for the given name.  Fails if no definition can
-- be found.
getDefinition :: Signature t -> Name -> Closed (Definition t)
getDefinition sig name =
    case HMS.lookup name (sDefinitions sig) of
      Nothing   -> error $ "impossible.getDefinition: not found " ++ show name
      Just def' -> def'

-- | Adds a new definition.
--
-- In the case of a new 'Projection' or 'DataCon', the definition of the
-- type constructor will be updated with the new information.  Fails if
-- the definition for the type constructor is not present.
addDefinition :: Signature t -> Name -> Closed (Definition t) -> Signature t
addDefinition sig name def' = case def' of
    Projection projIx tyCon _ -> addProjection tyCon projIx
    DataCon tyCon _           -> addDataCon tyCon
    _                         -> sig'
  where
    sig' = sig{sDefinitions = HMS.insert name def' (sDefinitions sig)}

    addProjection tyCon projIx = case getDefinition sig' tyCon of
      Constant (Record dataCon projs) tyConType ->
        let projs' = projs ++ [(name, projIx)]
            defs   = HMS.insert tyCon (Constant (Record dataCon projs') tyConType) (sDefinitions sig')
        in sig'{sDefinitions = defs}
      _ ->
        error $ "impossible.addDefinition: " ++ render tyCon ++ " is not a record"

    addDataCon tyCon = case getDefinition sig' tyCon of
      Constant (Data dataCons) tyConType ->
        let dataCons' = dataCons ++ [name]
            defs      = HMS.insert tyCon (Constant (Data dataCons') tyConType) (sDefinitions sig')
        in sig'{sDefinitions = defs}
      Constant (Record dataCon _) _ ->
        if name == dataCon
        then sig'
        else error $ "impossible.addDefinition: mismatching constructors " ++
                     render name ++ " and " ++ render dataCon
      _ ->
        error $ "impossible.addDefinition: " ++ render tyCon ++ " is not a data type"

definedNames :: Signature t -> [Name]
definedNames = HMS.keys . sDefinitions

-- | Gets the type of a 'MetaVar'.  Fails if the 'MetaVar' if not
-- present.
getMetaVarType :: Signature t -> MetaVar -> Closed (Type t)
getMetaVarType sig mv =
    case HMS.lookup mv (sMetasTypes sig) of
      Nothing -> error $ "impossible.getMetaVarType: not found " ++ show mv
      Just d -> d

-- | Gets the body of a 'MetaVar', if present.
getMetaVarBody :: Signature t -> MetaVar -> Maybe (Closed (Term t))
getMetaVarBody sig mv = HMS.lookup mv (sMetasBodies sig)

-- | Creates a new 'MetaVar' with the provided type.
addMetaVar :: Signature t -> Closed (Type t) -> (MetaVar, Signature t)
addMetaVar sig type_ =
    (mv, sig{ sMetasTypes = HMS.insert mv type_ (sMetasTypes sig)
            , sMetasCount = sMetasCount sig + 1
            })
  where
    mv = MetaVar $ sMetasCount sig

-- | Instantiates the given 'MetaVar' with the given body.  Fails if no
-- type is present for the 'MetaVar'.
instantiateMetaVar :: Signature t -> MetaVar -> Closed (Term t) -> Signature t
instantiateMetaVar sig mv _ | not (HMS.member mv (sMetasTypes sig)) =
  error $ "impossible.instantiateMetaVar: " ++ show mv ++ " not present."
instantiateMetaVar sig mv term =
  sig{sMetasBodies = HMS.insert mv term (sMetasBodies sig)}

-- | Gets the types of all 'MetaVar's.
metaVarsTypes :: Signature t -> HMS.HashMap MetaVar (Closed (Type t))
metaVarsTypes = sMetasTypes

-- | Gets the bodies for the instantiated 'MetaVar's.
metaVarsBodies :: Signature t -> HMS.HashMap MetaVar (Closed (Term t))
metaVarsBodies = sMetasBodies

-- Quickly redefining useful type synonyms...
---------------------------------------------

type Closed t = t Void
type Type (t :: * -> *) = t
type Term (t :: * -> *) = t
