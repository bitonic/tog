{-# LANGUAGE OverloadedStrings #-}
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
    , unsafeRemoveMetaVar
    , metaVarsTypes
    , metaVarsBodies
      -- * Utils
    , toScope
    ) where

import qualified Data.HashMap.Strict              as HMS
import qualified Data.Map.Strict                  as Map

import           Syntax
import           Term.Synonyms
import           Term.Types
import           PrettyPrint                      (render)

empty :: Signature t
empty = Signature HMS.empty HMS.empty HMS.empty 0

-- | Gets a definition for the given name.
getDefinition :: Signature t -> Name -> Maybe (Closed (Definition t))
getDefinition sig name = HMS.lookup name (sigDefinitions sig)

-- | Adds a new definition.
--
-- In the case of a new 'Projection' or 'DataCon', the definition of the
-- type constructor will be updated with the new information.  Fails if
-- the definition for the type constructor is not present.
addDefinition :: Signature t -> Name -> Closed (Definition t) -> Signature t
addDefinition sig defName def' = case (defName, def') of
    (name, Projection projIx tyCon _ _) -> addProjection name tyCon projIx
    (name, DataCon tyCon _ _ _)         -> addDataCon name tyCon
    _                                   -> sig'
  where
    sig' = sig{sigDefinitions = HMS.insert defName def' (sigDefinitions sig)}

    addProjection name tyCon projIx = case getDefinition sig' tyCon of
      Just (Constant tyConType (Record dataCon projs)) ->
        let projs' = projs ++ [Projection' name projIx]
            defs   = HMS.insert tyCon (Constant tyConType (Record dataCon projs')) (sigDefinitions sig')
        in sig'{sigDefinitions = defs}
      _ ->
        error $ "impossible.addDefinition: " ++ render tyCon ++ " is not a record"

    addDataCon name tyCon = case getDefinition sig' tyCon of
      Just (Constant tyConType (Data dataCons)) ->
        let dataCons' = dataCons ++ [name]
            defs      = HMS.insert tyCon (Constant tyConType (Data dataCons')) (sigDefinitions sig')
        in sig'{sigDefinitions = defs}
      Just (Constant _ (Record dataCon _)) ->
        if name == dataCon
        then sig'
        else error $ "impossible.addDefinition: mismatching constructors " ++
                     render name ++ " and " ++ render dataCon
      _ ->
        error $ "impossible.addDefinition: " ++ render tyCon ++ " is not a data type"

definedNames :: Signature t -> [Name]
definedNames = HMS.keys . sigDefinitions

-- | Gets the type of a 'MetaVar'.  Fails if the 'MetaVar' if not
-- present.
getMetaVarType :: Signature t -> MetaVar -> Closed (Type t)
getMetaVarType sig mv =
    case HMS.lookup mv (sigMetasTypes sig) of
      Nothing -> error $ "impossible.getMetaVarType: not found " ++ show mv
      Just d -> d

-- | Gets the body of a 'MetaVar', if present.
getMetaVarBody :: Signature t -> MetaVar -> Maybe (MetaVarBody t)
getMetaVarBody sig mv = HMS.lookup mv (sigMetasBodies sig)

-- | Creates a new 'MetaVar' with the provided type.
addMetaVar :: Signature t -> SrcLoc -> Closed (Type t) -> (MetaVar, Signature t)
addMetaVar sig loc type_ =
    (mv, sig{ sigMetasTypes = HMS.insert mv type_ (sigMetasTypes sig)
            , sigMetasCount = sigMetasCount sig + 1
            })
  where
    mv = MetaVar (sigMetasCount sig) loc

-- | Instantiates the given 'MetaVar' with the given body.  Fails if no
-- type is present for the 'MetaVar'.
instantiateMetaVar :: Signature t -> MetaVar -> MetaVarBody t -> Signature t
instantiateMetaVar sig mv _ | not (HMS.member mv (sigMetasTypes sig)) =
  error $ "impossible.instantiateMetaVar: " ++ show mv ++ " not present."
instantiateMetaVar sig mv term =
  sig{sigMetasBodies = HMS.insert mv term (sigMetasBodies sig)}

-- | Use with caution: this is safe only is said metavariable is not
-- referenced anywhere.
unsafeRemoveMetaVar :: Signature t -> MetaVar -> Signature t
unsafeRemoveMetaVar sig mv =
  let bodies = HMS.delete mv $ sigMetasBodies sig
      types  = HMS.delete mv $ sigMetasTypes sig
  in sig{sigMetasBodies = bodies, sigMetasTypes = types}

-- | Gets the types of all 'MetaVar's.
metaVarsTypes :: Signature t -> HMS.HashMap MetaVar (Closed (Type t))
metaVarsTypes = sigMetasTypes

-- | Gets the bodies for the instantiated 'MetaVar's.
metaVarsBodies :: Signature t -> HMS.HashMap MetaVar (MetaVarBody t)
metaVarsBodies = sigMetasBodies

toScope :: Signature t -> Scope
toScope = Scope . Map.fromList . map f . HMS.toList . sigDefinitions
  where
    f (n, def') = (nameString n, definitionToNameInfo n def')
