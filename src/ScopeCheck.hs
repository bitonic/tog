{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
-- | All scope checking is done in some module, say M.
--
-- We indicates new mappings from qualified or unqualified names to
-- fully-qualified names with @name ↦ qname@.  When saying @foo ↦ bar@
-- must be in scope, it means that either @foo@ is a fully qualified
-- name which is in scope, in which case @bar = foo@; or that @foo@ maps
-- to some fully qualified name @bar@.
--
-- We omit the treatment of implicit arguments, which is quite
-- straightforward.
--
-- == Type signatures
--
-- > foo : A
--
-- @A@ is scope-checked.  @foo ↦ M.foo@ is now in scope as a definition.
--
-- == Function definitions
--
-- > foo <pats> = <body>
-- >   where
-- >     <decls>
-- > foo ⋯
--
-- @foo@ must be in scope.  After putting the variable in @\<pats\>@ in
-- scope as variables, the @\<decls\>@ are scope-checked in module
-- @M.foo@.  @\<body\>@ is then scope-checked in the resulting
-- environment.
--
-- == Data declaration
--
-- > data D : Γ -> Set
--
-- @Γ -> Set@ is scope-checked.  @D ↦ M.D@ is now in scope.
--
-- == Data definition
--
-- > data D x₁ ⋯ xₙ where
-- >   c₁ : Γ₁ -> D x₁ ⋯ xₙ
-- >    ⋮
-- >   cₘ : Γₘ -> D x₁ ⋯ xₙ
--
-- @D@ must be in scope as a definition.  @x₁ ⋯ xₙ@ are put into scope
-- as variables, and every every @Γⱼ → D x₁ ⋯ xₙ@ is scope-checked.  The
-- return type for each them must be syntactically equal to @D x₁ ⋯ xₙ@.
-- For every @cⱼ@, @cⱼ ↦ M.cⱼ@ are now in scope as constructors -- after
-- all of them have been scope-checked.
--
-- == Record declaration
--
-- > record D : Γ -> Set
--
-- @Γ -> Set@ is scope-checked.  @D ↦ M.D@ is now in scope as a
-- definition.
--
-- == Record definition
--
-- > record D x₁ ⋯ xₙ where
-- >   constructor c
-- >   field
-- >     f₁ : A₁
-- >      ⋮
-- >     fₘ : Aₘ
--
-- @D@ must be in scope as a definition.  @x₁ ⋯ xₙ@ are put into scope
-- as variables, and each field type @Aⱼ@ is scope-checked in order.  As
-- soon as @fⱼ@ is scope-checked, we add @fⱼ ↦ M.fⱼ@ into the scope as a
-- projection, and we keep scope-checking the fields.  In other words,
-- every field has in scope all the previous ones.
--
-- Additionally, at the end, @c@ is in scope as a constructor.
--
-- == Postulates
--
-- > postulate foo : A
--
-- @A@ is scope-checked.  @foo ↦ M.foo@ is now in scope.
--
-- == Module declaration
--
-- > module N Γ (n₁ ⋯ nₙ) where
-- >   <decls>
--
-- @\<decls\>@ are scope-checked in module @M.N@.  @N ↦ M.N@ is now in
-- scope as a module, with exported names @n₁ ⋯ nₙ@.
--
-- Each exported name must be in scope when finishing type-checking the
-- declarations in the module.  If the list of exported names is not
-- present, a list is automatically generated using everything defined
-- name in the module.  For example, if @N@ contains
--
--
-- > postulate foo : A
--
-- @foo@ will be in the automatic export list, but if it contains
--
-- > open P
--
-- where @P@ is some other module, the names in @P@ will not be present
-- in the export list.
--
-- Additionally, if @Γ@ is empty, after the @module@ declaration an
-- @import N@ declaration will be automatically inserted after the
-- module declaration.  In other words, modules with no parameters are
-- automatically imported.
--
-- == Module imports
--
-- > import N t₁ ⋯ tₙ
--
-- @N@ must be in scope as a module.  All the exported names in @N@ are
-- added to the scope in their __qualified__ form.  For example, if @N@
-- exports @foo@ and @bar@, @N.foo@ and @N.bar@ are now in scope.
--
-- Additionally, if @N@ contains non parametrised modules, they are
-- automatically imported when @N@ is imported.  For example:
--
-- > module A where
-- >   module B where
-- >     ⋮
-- >   ⋮                          -- A.B automatically imported
-- > ⋮                            -- A and A.B automatically imported
--
-- > module A (x : Bool) where
-- >   module B where
-- >     ⋮
-- >   ⋮                           -- A.B automatically imported
-- > ⋮                             -- Nothing is imported
-- > import A true
-- > ⋮                             -- A imported and so A.B automatically imported
--
-- > module A where
-- >   module B (x : Bool) where
-- >     ⋮
-- >   ⋮                           -- Nothing is imported
-- > ⋮                             -- A automatically imported
-- > import A.B true
-- > ⋮                             -- Now A.B is imported too.
--
-- Note that @import@ brings the qualified names into scope only.
--
-- == Module openings
--
-- > open N
--
-- @N ↦ P@ must be already in scope as a module, and @P@ must be
-- imported.  Now all the exported names in @P@ are available
-- unqualified.
--
-- Note that if P contains, say
--
-- > module Q where
-- >   ⋮
--
-- While before the names in @Q@ were available as @N.Q.blah@, now they
-- are available as @Q.blah@, not as @blah@.
--
-- = Shadowing
--
-- Only variable bindings can shadow.  Every other name binding fails if
-- another thing (anything) is in scope with the same name, with only
-- one exception: @open@ed things.  In that case, multiple things with
-- the same name can be in scope, and you'll get an "ambiguous name"
-- error when trying to use them.
--
-- = Resolution
--
-- When resolving some name @n@ in a module, we have two cases:
--
-- * __Unqualified name__: we look at the variables, local definitions,
--   and @open@ed things.  As remarked in the "Shadowing" section, the
--   first two are unambiguous, and if a matching name is found, we know
--   that there isn't going to be an @open@ed name with the same name.
--
--   On the other hand, @open@ed names can be ambiguous: an error will
--   be thrown if that is the case.
--
--   If this procedure fails, and the module has a parent module, we
--   repeat by looking up in the parent module.
--
-- * __Qualified name__: If we have qualified name @M.f@, we check if
--   @M@ is imported, and if it is, we check if @f@ is in its exports.
--
-- = Qualification of names
--
-- Scope checking qualifies all non-variable names in the code, while
-- preserving module structure.  It also inserts @import@ statements
-- automatically for modules with no parameters.
--
-- So if we have
--
-- > module M where
-- >   module N where
-- >     postulate X : Set
-- >   open N
-- >   postulate bar : X -> X
--
-- scope checking will result in
--
-- > module M where
-- >   module M.N where
-- >     postulate M.N.foo : Set
-- >   import M.N
-- >   open M.N
-- >   postulate M.bar : M.N.X -> M.N.X
module ScopeCheck (scopeCheckModule, scopeCheckFile) where

import           Prelude hiding (length, replicate)

import           Control.Monad.Reader (MonadReader, ReaderT, runReaderT, local)
import           Control.Monad.Except (MonadError, throwError)
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Control.Lens as L
import           Control.Lens (at)
import           Data.List.NonEmpty (NonEmpty(..), (<|))

import           TogPrelude
import           Instrumentation
import           Names                            hiding (mkName)
import           Parse
import qualified Raw                              as C
import           Abstract
import qualified PrettyPrint                      as PP
import           PrettyPrint                      (render, Pretty(..), (<+>), ($$), (//>))

#include "impossible.h"

-- | The number of hidden parameters.
type Hiding = Natural

type NumberOfArguments = Natural

-- | Things defined in a module
type LocalNames = Map.Map Name NameInfo
type ExportedNames = Map.Map Name NameInfo

-- | Modules that should be auto-imported when the containing module is.
-- They are not prefixed by the containing module name. The 'Name's
-- contained should be a subset of the keys in 'Exports'.
type AutoImportModules = Set.Set Name

data NameInfo
  = DefName Hiding
  | ConName Hiding NumberOfArguments
  | ProjName Hiding
  | ModuleName Hiding ExportedNames AutoImportModules
  deriving (Show)

instance Pretty NameInfo where
  pretty ni = case ni of
    DefName hidden -> "DefName" <+> pretty  hidden
    ConName hidden args -> "ConName" <+> pretty hidden <+> pretty args
    ProjName hidden -> "ProjName" <+> pretty hidden
    ModuleName hidden names autoImports ->
      "ModuleName" <+> pretty hidden <+> pretty autoImports $$ "exports:" //> pretty names

-- | Useful type synonym to indicate that a name is fully qualified.
type FullyQName = QName

data Scope = Scope
  { _sVars :: Map.Map Name SrcLoc
    -- ^ The variables in scope
  , _sNameSpace :: NameSpace
    -- ^ The namespace for the current module
  , _sParentNameSpaces :: [NameSpace]
    -- ^ The namespaces for the parent modules
  , _sOpenedNames :: Map.Map Name (NonEmpty FullyQName)
    -- ^ Mapping that stores "opened" names to some fully qualified
    -- name.  If multiple, it means that we have an ambiguous name.
  , _sImportedModules :: Map.Map FullyQName (Hiding, ExportedNames)
    -- ^ The imported modules, from the "local" name to the fully
    -- qualified name.
  }

data NameSpace = NameSpace
  { _nsModule :: FullyQName
  , _nsLocalNames :: LocalNames
    -- ^ The definitions defined in some module.
  , _nsAutoImports :: AutoImportModules
    -- ^ The modules in the current module that should be automatically
    -- imported.
  }

makeLenses ''Scope
makeLenses ''NameSpace

data ScopeError = ScopeError SrcLoc String
  deriving (Show)

instance Pretty ScopeError where
  pretty (ScopeError pos err) = pretty pos <> ":" <+> PP.text err

initNameSpace :: FullyQName -> NameSpace
initNameSpace qn = NameSpace qn Map.empty Set.empty

initScope :: FullyQName -> Scope
initScope n = Scope Map.empty (initNameSpace n) [] Map.empty Map.empty

newtype Check a = Check { unCheck :: ReaderT Scope (Either ScopeError) a }
  deriving (Functor, Applicative, Monad, MonadReader Scope, MonadError ScopeError)

evalCheck :: Scope -> Check a -> Either ScopeError a
evalCheck sc m = runReaderT (unCheck m) sc

type CCheck a = forall b. (a -> Check b) -> Check b
type CCheck_ = forall b. Check b -> Check b

mapC :: (a -> CCheck b) -> [a] -> CCheck [b]
mapC _ [] ret = ret []
mapC f (x : xs) ret = f x $ \y -> mapC f xs $ \ys -> ret (y : ys)

mapC_ :: (a -> CCheck_) -> [a] -> CCheck_
mapC_ _ [] ret = ret
mapC_ f (x : xs) ret = f x $ mapC_ f xs ret

concatMapC :: (a -> CCheck [b]) -> [a] -> CCheck [b]
concatMapC f xs ret = mapC f xs $ ret . concat

scopeError :: HasSrcLoc i => i -> String -> Check a
scopeError p err = throwError $ ScopeError (srcLoc p) err

------------------------------------------------------------------------
-- Binding/resolving things

lookupInNameSpaces
  :: (NameSpace -> Check (Maybe a))
  -> Check (Maybe a)
lookupInNameSpaces f = do
  ns <- L.view sNameSpace
  nss <- L.view sParentNameSpaces
  go (ns : nss)
  where
    go [] = return Nothing
    go (ns : nss) = do
      mb <- f ns
      case mb of
        Just x  -> return $ Just x
        Nothing -> go nss

isBoundVar
  :: Name -> Check Bool
isBoundVar n = Map.member n <$> L.view sVars

checkShadowing :: Name -> Check ()
checkShadowing n = do
  mbVar <- L.view $ sVars . at n
  forM_ mbVar $ \loc ->
    scopeError n $ "Cannot shadow " ++ render n ++ ", variable bound at " ++ render loc
  definedLocally <- lookupLocalName n
  forM_ definedLocally $ \(qn, _) -> do
    scopeError n $ "Cannot shadow " ++ render qn ++ ", defined at " ++ render (srcLoc qn)

lookupLocalName
  :: Name -> Check (Maybe (FullyQName, NameInfo))
lookupLocalName n = do
  lookupInNameSpaces $ \ns -> return $
    (qNameCons n (ns^.nsModule),) <$> ns^.nsLocalNames^.at n

lookupOpenedName
  :: Name -> Check (Maybe (FullyQName, NameInfo))
lookupOpenedName n = do
  mbNames <- L.view $ sOpenedNames . at n
  case mbNames of
    Nothing        -> return Nothing
    Just (x :| []) -> do Just ni <- lookupFullyQName x
                         return $ Just (x, ni)
    Just (x :| xs) -> err (x : xs)
  where
    err :: [FullyQName] -> Check a
    err xs = scopeError n $ render n ++ " could be any of " ++ render xs

lookupFullyQName :: FullyQName -> Check (Maybe NameInfo)
lookupFullyQName (QName n ~(m:ms)) = do
  Just (_, exports) <- L.view $ sImportedModules . at (QName m ms)
  return $ Map.lookup n exports

qualifyName
  :: Name -> Check FullyQName
qualifyName n = do
  mn <- L.view $ sNameSpace . nsModule
  return $ qNameCons n mn

bindLocalName
  :: Name -> NameInfo -> CCheck FullyQName
bindLocalName n ni ret = do
  checkShadowing n
  qn <- qualifyName n
  local (L.set (sNameSpace . nsLocalNames . at n) (Just ni)) $ ret qn

-- | Accepts a list of new bindings to add to the list of opened names.
-- Fails if we'd have to shadow un-shadowable things -- variables and
-- local names.
bindOpenedNames :: [(Name, FullyQName)] -> CCheck_
bindOpenedNames = mapC_ $ \(n, qn) ret -> do
  checkShadowing n
  local (over (sOpenedNames . at n) (Just . maybe (qn :| []) (qn <|))) ret

bindDef :: Name -> Hiding -> CCheck FullyQName
bindDef n hidden = bindLocalName n $ DefName hidden

bindProj :: Name -> Hiding -> CCheck FullyQName
bindProj n hidden = bindLocalName n $ ProjName hidden

bindVar :: Name -> CCheck Name
bindVar n ret = do
  local (over sVars (Map.insert n (srcLoc n))) $ ret n

notInScopeError :: (PP.Pretty name, HasSrcLoc name) => name -> Check a
notInScopeError n = scopeError n $ render n ++ " not in scope"

resolveLocalName :: Name -> Check (FullyQName, NameInfo)
resolveLocalName n = do
  mb <- lookupLocalName n
  case mb of
    Nothing -> notInScopeError n
    Just x  -> return x

resolveLocalDef :: Name -> Check (FullyQName, Hiding)
resolveLocalDef n = do
  ln <- resolveLocalName n
  case ln of
    (qn, DefName hidden) -> return (qn, hidden)
    _ -> scopeError n $ render n ++ " should be a definition"

data LookupQName
  = NotFound
  | ItsAVar Name
  | ItsANameInfo FullyQName NameInfo

instance Pretty LookupQName where
  pretty lkup = case lkup of
    NotFound -> "NotFound"
    ItsAVar v -> "ItsAVar" <+> pretty v
    ItsANameInfo qn ni -> "ItsANameInfo" <+> pretty qn $$ "info:" //> pretty ni

lookupQName :: QName -> Check LookupQName
lookupQName (QName n []) = do
  isVar <- isBoundVar n
  if isVar
    then return $ ItsAVar n
    else do
      mbLocal <- lookupLocalName n
      case mbLocal of
        Just (qn, ni) -> return $ ItsANameInfo qn ni
        Nothing -> do
          mbOpened <- lookupOpenedName n
          case mbOpened of
            Just (qn, ni) -> return $ ItsANameInfo qn ni
            Nothing -> return NotFound
lookupQName (QName n (m:ms)) = do
  (moduleQn, _, names, _) <- resolveImportedModule $ QName m ms
  case Map.lookup n names of
    Nothing -> return NotFound
    Just ni -> return $ ItsANameInfo (qNameCons n moduleQn) ni

importModule
  :: QName -> Hiding -> ExportedNames -> CCheck_
importModule qn hidden names ret = do
  mb <- L.view $ sImportedModules . at qn
  case mb of
    Just _ -> scopeError qn $ render qn ++ " already imported"
    Nothing -> local (L.set (sImportedModules . at qn) (Just (hidden, names))) ret

resolveModule :: QName -> Check (FullyQName, Hiding, ExportedNames, AutoImportModules)
resolveModule m = do
  lkup <- lookupQName m
  case lkup of
    NotFound -> notInScopeError m
    ItsANameInfo qn (ModuleName hidden names autoImports) -> return (qn, hidden, names, autoImports)
    _ -> scopeError m $ render m ++ " should be a module"

resolveCon :: QName -> Check (FullyQName, Hiding, NumberOfArguments)
resolveCon m = do
  lkup <- lookupQName m
  case lkup of
    NotFound -> notInScopeError m
    ItsANameInfo qn (ConName hidden args) -> return (qn, hidden, args)
    _ -> scopeError m $ render m ++ " should be a data constructor"

resolveImportedModule :: QName -> Check (FullyQName, Hiding, ExportedNames, AutoImportModules)
resolveImportedModule n = do
  (qn, hidden, names, autoImports) <- resolveModule n
  isImported <- isJust <$> L.view (sImportedModules . at qn)
  unless isImported $
    scopeError n $ render n ++ " should be imported"
  return (qn, hidden, names, autoImports)

------------------------------------------------------------------------
-- Scope checking

-- | Scope checks a top-level module.
scopeCheckModule :: C.Module -> Either PP.Doc Module
scopeCheckModule (C.Module (C.Name ((l, c), s)) pars ds) =
  case evalCheck (initScope q) (checkModule' q pars ds return) of
    Left err -> Left $ pretty err
    Right (x, _) -> Right x
  where
    q = QName (Name (SrcLoc l c) s) []

-- Useful for debugging.
scopeCheckFile :: FilePath -> IO ()
scopeCheckFile fp = do
  s <- readFile fp
  case parseModule s of
    Left err -> putStrLn $ render err
    Right raw -> case scopeCheckModule raw of
      Left err -> putStrLn $ render err
      Right abs -> putStrLn $ render abs

-- | Scope checks a module.  Returns the generated module, and possibly
-- some declarations containing auto-imports and the like.
checkModule :: C.Module -> CCheck (Module, [C.Decl])
checkModule (C.Module name pars ds) ret = do
  name <- return $ mkName name
  -- Qualify the name of the module
  qname <- qualifyName name
  checkModule' qname pars ds ret

checkModule' :: QName -> C.Params -> [C.Decl] -> CCheck (Module, [C.Decl])
checkModule' qname@(QName name _) pars ds ret = do
  case isParamDecl pars of
    Just pars -> do
      -- Push a fresh NameSpace for the new module.
      let prepareScope sc = L.over sParentNameSpaces (sc^.sNameSpace :)
                          $ L.set sNameSpace (initNameSpace qname) sc
      (moduleInfo, module_) <- local prepareScope $ do
        -- Check the parameters and add them to the scope
        (hidden, pars, _) <- return $ telHiding pars
        checkTel pars $ \tel -> do
          -- Check the declarations
          checkDecls ds $ \ds -> do
            -- Return the 'NameInfo' containing the generated definitions
            -- and auto importing modules, and the 'Module' itself
            -- containing the fully qualified name and exports, the
            -- parameters, and the declarations.
            definitions <- L.view $ sNameSpace . nsLocalNames
            let qdefinitions = map (`qNameCons` qname) $ Map.keys definitions
            -- Store the auto imports
            autoImports <- L.view $ sNameSpace . nsAutoImports
            return
              ( ModuleName hidden definitions autoImports
              , Module qname tel qdefinitions ds
              )
      bindLocalName name moduleInfo $ \_ ->
        if null pars
          then -- Add it to the auto imports list, and return with the decl
               local (over (sNameSpace . nsAutoImports) (Set.insert name)) $
               ret (module_, [mkRawImportDecl (QName name [])])
          else ret (module_, [])
    Nothing ->
      scopeError name "Bad module declaration"

checkDecls :: [C.Decl] -> CCheck [Decl]
checkDecls ds ret = case ds of
  [] ->
    ret []
  C.Postulate [] : ds ->
    checkDecls ds ret
  C.Postulate (sig : sigs) : ds ->
    checkTypeSig sig $ \sig -> do
      checkDecls (C.Postulate sigs : ds) $ \ds -> do
        ret (Postulate sig : ds)
  C.TypeSig sig : ds -> do
    checkTypeSig sig $ \sig -> do
      checkDecls ds $ \ds -> do
        ret (TypeSig sig : ds)
  C.Data x pars mbDataBody : ds -> case mbDataBody of
    C.DataDecl set -> case isParamDecl pars of
      Nothing -> scopeError x $ "Bad data declaration " ++ C.printTree x
      Just ps -> checkDataOrRecDecl x ps set $ \sig -> do
                   checkDecls ds $ \ds -> do
                     ret (Data sig : ds)
    C.DataDef cs -> case isParamDef pars of
      Nothing -> do
        scopeError x "Bad data declaration"
      Just xs -> do
        (x, n) <- resolveLocalDef $ mkName x
        when (n > length xs) $
          scopeError x $ "Too few parameters to " ++ render x ++
                         " (implicit arguments must be explicitly bound here)"
        xs <- checkHiddenNames n xs
        xs <- return $ map mkName xs
        cs <- mapC bindVar xs $ \xs -> do
          let t = App (Def x) (map (\x -> Apply (App (Var x) [])) xs)
          mapM (checkConstructor t xs) cs
        let bindCon (c, ni, a) ret = bindLocalName c ni $ \qn -> ret $ Sig qn a
        mapC bindCon cs $ \cs ->
          checkDecls ds $ \ds' -> ret (DataDef x xs cs : ds')
    C.DataDeclDef set cs -> case isParamDecl pars of
      Nothing ->
        scopeError x $ "Bad data declaration"
      Just bindings -> do
        -- If we got a parameter declaration and a body, split this into
        -- two.
        xs <- mkHiddenNames bindings
        let ds' = C.Data x pars (C.DataDecl set) :
                  C.Data x (C.ParamDef xs) (C.DataDef cs):
                  ds
        checkDecls ds' ret
  C.Record x pars mbRecBody : ds -> case mbRecBody of
    C.RecordDecl set -> case isParamDecl pars of
      Nothing -> scopeError x $ "Bad record declaration " ++ C.printTree x
      Just ps -> checkDataOrRecDecl x ps set $ \sig -> do
                   checkDecls ds $ \ds -> do
                     ret (Record sig : ds)
    C.RecordDef con fs -> case isParamDef pars of
      Nothing -> do
        scopeError x $ "Bad record definition"
      Just xs -> do
        (x, n) <- resolveLocalDef $ mkName x
        when (n > length xs) $
          scopeError x $ "Too few parameters to " ++ show x ++
                         " (implicit arguments must be explicitly bound here)"
        xs <- checkHiddenNames n xs
        xs <- return $ map mkName xs
        (con, ni, fs) <- mapC bindVar xs $ \_ -> do
          checkFields (getFields fs) $ \fs ->
            return (mkName con, ConName 0 (length fs), fs)
        bindLocalName con ni $ \con -> do
          let bindProj (f, ni, a) ret = bindLocalName f ni $ \qn -> ret $ Sig qn a
          mapC bindProj fs $ \fs -> do
            checkDecls ds $ \ds' -> do
              ret (RecDef x xs con fs : ds')
    C.RecordDeclDef set con fs -> case isParamDecl pars of
      Nothing -> do
        scopeError x $ "Bad record definition"
      Just bindings -> do
        xs <- mkHiddenNames bindings
        let ds' = C.Record x pars (C.RecordDecl set) :
                  C.Record x (C.ParamDef xs) (C.RecordDef con fs):
                  ds
        checkDecls ds' ret
  C.FunDef f _ _ _ : _ -> do
    (clauses, ds) <- return $ takeFunDefs f ds
    (f, n) <- resolveLocalDef $ mkName f
    clauses <- forM (zip clauses [1..]) $ \((ps, body, wheres0), ix) -> do
      let wheres = case wheres0 of
            C.Where ds -> ds
            C.NoWhere  -> []
      ps <- insertImplicitPatterns (srcLoc f) n ps
      mapC checkPattern ps $ \ps -> do
        checkWheres f ix wheres $ \wheres -> do
          body <- checkExpr body
          return $ Clause ps body wheres
    checkDecls ds $ \ds -> ret (FunDef f clauses : ds)
  C.Module_ module_ : ds -> do
    checkModule module_ $ \(module_, moduleDs) -> do
      checkDecls (moduleDs ++ ds) $ \ds -> do
        ret (Module_ module_ : ds)
  C.Import imp : ds -> do
    let (m, args) = case imp of
          C.ImportNoArgs m    -> (mkQName m, [])
          C.ImportArgs m args -> (mkQName m, args)
    (qn, hidden, names, autoImports) <- resolveModule m
    args <- insertImplicit (srcLoc m) hidden args
    args <- mapM checkExpr args
    -- Add the module to the set of imported modules
    importModule qn hidden names $ do
      -- Import the modules to auto import
      let autoImportsDecls = map (\n -> mkRawImportDecl (qNameCons n m)) $ Set.toList autoImports
      checkDecls (autoImportsDecls ++ ds) $ \ds -> do
        ret (Import qn args : ds)
  C.Open m0 : ds -> do
    let m = mkQName m0
    (m, _, exports, _) <- resolveImportedModule m
    let opened = [(n, qNameCons n m) | (n, _) <- Map.toList exports]
    bindOpenedNames opened $ do
      checkDecls ds $ \ds -> do
        ret (Open m : ds)
  C.OpenImport imp : ds -> do
    let m = case imp of
          C.ImportNoArgs m -> m
          C.ImportArgs m _ -> m
    checkDecls (C.Import imp : C.Open m : ds) ret
  where
    takeFunDefs :: C.Name -> [C.Decl] -> ([([C.Pattern], C.Expr, C.Where)], [C.Decl])
    takeFunDefs _ [] =
      ([], [])
    takeFunDefs f (C.FunDef f' ps b wheres : ds) | sameName f f' =
      first ((ps, b, wheres) :) $ takeFunDefs f ds
    takeFunDefs _ d =
      ([], d)

    sameName (C.Name (_, f1)) (C.Name (_, f2)) = f1 == f2

checkWheres :: QName -> Natural -> [C.Decl] -> CCheck [Decl]
checkWheres f ix ds ret = do
  -- We scope-check the wheres in a module for the function, plus an
  -- index for the clause.  Then, we save the 'sNameInfos' and the
  -- 'sOpenedNames', so that when scope-checking the body we'll have
  -- what we need in scope, but we throw away everything else.
  let qname = qNameCons (Name (srcLoc f) (show ix)) f
  let prepareScope sc = L.over sParentNameSpaces (sc^.sNameSpace :)
                      $ L.set sNameSpace (initNameSpace qname) sc
  local prepareScope $ checkDecls ds ret

checkTypeSig :: C.TypeSig -> CCheck TypeSig
checkTypeSig (C.Sig x e) ret = do
  (n, a) <- checkScheme e
  bindDef (mkName x) n $ \x -> ret (Sig x a)

checkFields :: [C.Constr] -> CCheck [(Name, NameInfo, Expr)]
checkFields fs ret = do
  fs <- mapC checkField fs return
  mapC bindField fs ret
  where
    bindField :: (C.Name, Natural, Expr) -> CCheck (Name, NameInfo, Expr)
    bindField (x, n, a) ret = do
      x <- return $ mkName x
      bindProj x n $ \_ -> ret (x, ProjName n, a)

checkField :: C.Constr -> CCheck (C.Name, Natural, Expr)
checkField (C.Constr c e) ret = do
  (n, a) <- checkScheme e
  bindVar (mkName c) $ \_ -> ret (c, n, a)

checkDataOrRecDecl
  :: C.Name -> [C.Binding] -> C.Name -> CCheck TypeSig
checkDataOrRecDecl x ps set ret = do
  isSet set
  (n, a) <- checkScheme (C.Pi (C.Tel ps) (C.App [C.Arg $ C.Id $ C.NotQual set]))
  bindDef (mkName x) n $ \x -> ret $ Sig x a

checkTel :: [C.Binding] -> CCheck Params
checkTel = concatMapC checkBinding

checkBinding :: C.Binding -> CCheck [(Name, Expr)]
checkBinding b@C.HBind{} _ = scopeError b $ "Implicit binding must be on top level: " ++ C.printTree b
checkBinding (C.Bind args e) ret = do
  xs <- mapM argName args
  a <- checkExpr e
  mapC (bindVar . mkName) xs $ \ys -> ret [ (y, a) | y <- ys ]

argName :: C.Arg -> Check C.Name
argName (C.Arg (C.Id (C.NotQual x))) = return x
argName a = scopeError a $ "Expected variable name: " ++ C.printTree a

checkConstructor :: Expr -> [Name] -> C.Constr -> Check (Name, NameInfo, Expr)
checkConstructor d xs (C.Constr c e) = do
  (n, a) <- checkScheme e
  args   <- checkConstructorType a d xs
  return (mkName c, ConName n args, a)

checkConstructorType
  :: Expr
  -- ^ The constructor's type.
  -> Expr
  -- ^ The data type applied to its parameters.
  -> [Name]
  -- ^ The parameters.
  -> Check NumberOfArguments
  -- ^ The number of constructor arguments is returned.
checkConstructorType a d xs = check a
  where
  check (Fun _ b)  = succ <$> check b
  check (Pi x _ b) = do
    when (x `elem` xs) $
      scopeError a $ "Attempt to shadow data type parameter " ++ show x
    succ <$> check b
  check b
    | b == d    = return 0
    | otherwise = scopeError a $
                    "Not a well-formed constructor type: " ++ show a

checkScheme :: C.Expr -> Check (Hiding, Expr)
checkScheme e = do
  (n, e) <- checkHiding e
  a      <- checkExpr e
  return (n, a)

type PAppView = (C.QName,  [C.Pattern])

pAppView :: C.Pattern -> Check PAppView
pAppView p = case p of
  C.AppP p q -> applyTo q <$> pAppView p
  C.IdP x    -> return (x, [])
  C.HideP p  -> scopeError p $ "Unexpected implicit pattern: " ++ C.printTree p
  where
    applyTo q (c, ps) = (c, ps ++ [q])

checkPattern :: C.Pattern -> CCheck Pattern
checkPattern p ret = do
  (c, ps) <- pAppView p
  case (c, ps) of
    (C.NotQual (C.Name ((l, c), "_")), []) -> ret $ WildP (SrcLoc l c)
    (x, []) -> do
      -- The name in a pattern must be either a constructor or a variable.
      mbDef <- lookupQName $ mkQName x
      case (mbDef, x) of
        (ItsANameInfo _ ConName{}, _) -> checkCon x [] ret
        (_, C.NotQual n) -> bindVar (mkName n) $ ret. VarP
        (_, _) -> scopeError x $ C.printTree x ++ " not in scope"
    (c, ps) -> checkCon c ps ret
  where
    checkCon c0 ps ret = do
      let c = mkQName c0
      (c, n, args) <- resolveCon c
      ps <- insertImplicitPatterns (srcLoc c) n ps
      checkNumberOfConstructorArguments p c ps args
      mapC checkPattern ps $ \ps -> ret (ConP c ps)

checkNumberOfConstructorArguments ::
  HasSrcLoc e => e -> QName -> [a] -> NumberOfArguments -> Check ()
checkNumberOfConstructorArguments loc c as args = do
  when (nas < args) $
    scopeError loc $ "The constructor " ++ show c ++
                     " is applied to too few arguments."
  when (nas > args) $
    scopeError loc $ "The constructor " ++ show c ++
                     " is applied to too many arguments."
  where nas = length as

checkExpr :: C.Expr -> Check Expr
checkExpr e = case e of
  C.Pi (C.Tel tel) b ->
    checkTel tel $ \tel -> do
      b <- checkExpr b
      return $ foldr (uncurry Pi) b tel
  C.Fun a b -> Fun <$> checkExpr a <*> checkExpr b
  C.Lam xs e ->
    mapC (bindVar . mkName) xs $ \xs ->
    flip (foldr Lam) xs <$> checkExpr e
  C.Eq x y -> do
    x <- checkExpr x
    y <- checkExpr y
    return $ Equal (Meta $ srcLoc x) x y
  C.Id{}  -> checkApp e
  C.App{} -> checkApp e
  where
    checkApp e = do
      app <- appView e
      case app of
        NotApp e  -> checkExpr e
        CApp x es -> do
          (z, n) <- checkAppHead x
          case z of
            IsProj x -> case es of
              []   -> scopeError e $ "Record projections must be applied: " ++ C.printTree e
              C.HArg _ : _ -> scopeError e $ "Unexpected implicit argument to projection function: " ++ C.printTree e
              C.Arg e : es -> do
                e <- checkExpr e
                doProj x e n . map Apply =<< checkArgs e n es (\ _ -> return ())
            IsRefl p | [] <- es ->
              return $ Refl p
            IsRefl p ->
              scopeError p $ "refl applied to arguments " ++ show es
            IsCon c args -> do
              Con c <$> checkArgs z n es
                        (\es -> checkNumberOfConstructorArguments e c es args)
            Other h    -> App h . map Apply <$> checkArgs z n es (\ _ -> return ())
            HeadSet p  -> return $ Set p
            HeadMeta p -> return $ Meta p
    doProj x (App h es1) n es2 = return $ App h (es1 ++ [Proj x] ++ replicate n (Apply (Meta (srcLoc x))) ++ es2)
    doProj x e _ _ = scopeError x $ "Cannot project " ++ show x ++ " from " ++ show e

checkArgs :: HasSrcLoc a =>
             a -> Hiding -> [C.Arg] -> (forall b. [b] -> Check ()) ->
             Check [Expr]
checkArgs x n es extraCheck = do
  es <- insertImplicit (srcLoc x) n es
  extraCheck es
  mapM checkExpr es

data AppHead = IsProj QName
             | IsCon QName NumberOfArguments
             | IsRefl SrcLoc
             | Other Head
             | HeadSet SrcLoc
             | HeadMeta SrcLoc

data AppView = CApp C.QName [C.Arg]
             | NotApp C.Expr

appView :: C.Expr -> Check AppView
appView e = case e of
  C.App (arg@C.HArg{} : _) ->
    scopeError arg $ "Unexpected curly braces: " ++ C.printTree arg
  C.App (C.Arg e : es) -> applyTo es =<< appView e
  C.App []             -> __IMPOSSIBLE__
  C.Id x               -> return $ CApp x []
  C.Lam _ _            -> notApp
  C.Pi{}               -> notApp
  C.Fun{}              -> notApp
  C.Eq{}               -> notApp
  where
    notApp = return $ NotApp e
    applyTo []  app          = return app
    applyTo es2 (CApp x es1) = return $ CApp x $ es1 ++ es2
    applyTo _   (NotApp e)   = scopeError e $ C.printTree e ++ " cannot be applied to arguments"

checkAppHead :: C.QName -> Check (AppHead, Hiding)
checkAppHead qn = case qn of
  C.NotQual n -> case n of
    C.Name ((l, c), "_") -> return (HeadMeta $ SrcLoc l c, 0)
    C.Name ((l, c), "Set") -> return (HeadSet $ SrcLoc l c, 0)
    C.Name ((l, c), "J") -> return (Other (J (SrcLoc l c)), 3)
    C.Name ((l, c), "refl") -> return (IsRefl (SrcLoc l c), 0)
    _ -> fallback
  _ -> fallback
  where
    fallback = do
      varOrName <- lookupQName $ mkQName qn
      case varOrName of
        NotFound -> notInScopeError $ mkQName qn
        ItsAVar x -> return (Other $ Var x, 0)
        ItsANameInfo x i -> case i of
          ProjName n       -> return (IsProj x, n)
          ConName n a      -> return (IsCon x a, n)
          DefName n        -> return (Other $ Def x, n)
          ModuleName{}     -> scopeError x $ "Cannot use module name " ++ render x ++ " in term."

checkHiding :: C.Expr -> Check (Hiding, C.Expr)
checkHiding e = case e of
  C.Fun a b  -> second (C.Fun a) <$> checkHiding b
  C.Pi (C.Tel tel0) b -> do
    let (n, tel, stop) = telHiding tel0
    if stop then return (n, C.Pi (C.Tel tel) b)
            else do
      (m, b) <- checkHiding b
      return (n + m, C.Pi (C.Tel tel) b)
  _ -> return (0, e)

checkHiddenNames :: Hiding -> [C.HiddenName] -> Check [C.Name]
checkHiddenNames 0 (C.NotHidden x : xs) = (x :) <$> checkHiddenNames 0 xs
checkHiddenNames _ (C.NotHidden x : _)  = scopeError x $ "Expected implicit binding of " ++ C.printTree x
checkHiddenNames 0 (C.Hidden x : _)     = scopeError x $ "Expected explicit binding of " ++ C.printTree x
checkHiddenNames n (C.Hidden x : xs)    = (x :) <$> checkHiddenNames (n - 1) xs
checkHiddenNames 0 []                   = return []
checkHiddenNames _ []                   = __IMPOSSIBLE__

insertImplicit :: SrcLoc -> Hiding -> [C.Arg] -> Check [C.Expr]
insertImplicit _ 0 (C.Arg e : args)  = (e :) <$> insertImplicit (srcLoc e) 0 args
insertImplicit _ 0 (C.HArg e : _)    = scopeError e $ "Unexpected implicit application " ++ C.printTree e
insertImplicit _ 0 []                = return []
insertImplicit _ n (C.HArg e : args) = (e :) <$> insertImplicit (srcLoc e) (n - 1) args
insertImplicit p n args              = (cMeta p :) <$> insertImplicit p (n - 1) args

insertImplicitPatterns :: SrcLoc -> Hiding -> [C.Pattern] -> Check [C.Pattern]
insertImplicitPatterns _ 0 (C.HideP e : _)  = scopeError e $ "Unexpected implicit pattern " ++ C.printTree e
insertImplicitPatterns _ 0 (e : args)       = (e :) <$> insertImplicitPatterns (srcLoc e) 0 args
insertImplicitPatterns _ 0 []               = return []
insertImplicitPatterns _ n (C.HideP e : ps) = (e :) <$> insertImplicitPatterns (srcLoc e) (n - 1) ps
insertImplicitPatterns p n ps               = (cWild p :) <$> insertImplicitPatterns p (n - 1) ps

------------------------------------------------------------------------
-- Utils

mkName :: C.Name -> Name
mkName (C.Name ((l, c), s)) = Name (SrcLoc l c) s

mkQName :: C.QName -> QName
mkQName (C.NotQual n) = QName (mkName n) []
mkQName (C.Qual qn n) = case mkQName qn of
  QName n' m -> QName (mkName n) (n' : m)

telHiding :: [C.Binding] -> (Hiding, [C.Binding], Bool)
telHiding [] = (0, [], False)
telHiding bs@(C.Bind{} : _) = (0, bs, True)
telHiding (C.HBind xs e : bs0) =
  let (n, bs, stop) = telHiding bs0
  in (n + length xs, C.Bind xs e : bs, stop)

isParamDef :: C.Params -> Maybe [C.HiddenName]
isParamDef C.NoParams      = Just []
isParamDef C.ParamDecl{}   = Nothing
isParamDef (C.ParamDef xs) = Just xs

isParamDecl :: C.Params -> Maybe [C.Binding]
isParamDecl C.NoParams       = Just []
isParamDecl (C.ParamDecl ps) = Just ps
isParamDecl C.ParamDef{}     = Nothing

mkHiddenNames :: [C.Binding] -> Check [C.HiddenName]
mkHiddenNames xs = concat <$> mapM goBinding xs
  where
    goBinding (C.Bind args _) = map C.NotHidden <$> mapM argName args
    goBinding (C.HBind args _) = map C.Hidden <$> mapM argName args

isSet :: C.Name -> Check ()
isSet (C.Name (_, "Set")) = return ()
isSet e = scopeError e "The type of a datatype or record should be Set"

getFields :: C.Fields -> [C.Constr]
getFields C.NoFields    = []
getFields (C.Fields fs) = fs

cMeta :: HasSrcLoc a => a -> C.Expr
cMeta x = C.App [C.Arg $ C.Id $ C.NotQual $ C.Name ((l, c), "_")]
  where SrcLoc l c = srcLoc x

cWild :: HasSrcLoc a => a -> C.Pattern
cWild x = C.IdP (C.NotQual (C.Name ((l, c), "_")))
  where SrcLoc l c = srcLoc x

mkRawImportDecl :: QName -> C.Decl
mkRawImportDecl = C.Import . C.ImportNoArgs . toRawName
  where
    toRawName :: QName -> C.QName
    toRawName (QName n ns) = go $ n : ns
      where
        unMkName (Name (SrcLoc l c) s) = C.Name ((l, c), s)

        go []       = __IMPOSSIBLE__
        go [n]      = C.NotQual $ unMkName n
        go (n : ns) = C.Qual (go ns) $ unMkName n

------------------------------------------------------------------------
--  HasSrcLoc instances

instance HasSrcLoc AppHead where
  srcLoc h = case h of
    IsProj x     -> srcLoc x
    IsCon c _    -> srcLoc c
    IsRefl p     -> p
    Other h      -> srcLoc h
    HeadSet p    -> p
    HeadMeta p   -> p

