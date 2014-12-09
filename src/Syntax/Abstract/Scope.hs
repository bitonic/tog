{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing -fno-warn-orphans #-}
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
module Syntax.Abstract.Scope (scopeCheckModule, scopeCheckFile) where

import           Prelude hiding (length)

import           Control.Monad.Reader (MonadReader, ReaderT, runReaderT, local)
import           Control.Monad.Except (MonadError, throwError)
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Control.Lens as L
import           Data.List (inits, tails)
import qualified Data.Semigroup as Semi

import           Prelude.Extended
import           Instrumentation
import qualified Syntax.Raw                       as C
import           Syntax.Abstract.Abs
import qualified PrettyPrint                      as PP
import           PrettyPrint                      (render)

#include "impossible.h"

-- | The number of hidden parameters.
type Hiding = Natural

type NumberOfArguments = Natural

-- | Things defined in a module
type LocalNames = Map.Map Name NameInfo

-- | Modules that should be auto-imported when the containing module is.
-- They are not prefixed by the containing module name. The 'Name's
-- contained should be a subset of the keys in 'Exports'.
type AutoImportModules = Set.Set Name

data NameInfo
  = DefName Hiding
  | ConName Hiding NumberOfArguments
  | ProjName Hiding
  | ModuleName Hiding LocalNames AutoImportModules
  | AmbiguousName [QName]
  deriving (Show)

-- | Useful type synonym to indicate that a name is fully qualified.
type FullyQName = QName

data Scope = Scope
  { _sVars :: Set.Set String
    -- ^ The variables in scope
  , _sOpenedNames :: Map.Map String [FullyQName]
    -- ^ Mapping that stores "opened" names to some fully qualified
    -- name.  If multiple, it means that we have an ambiguous name.
  , _sImportedModules :: Set.Set FullyQName
    -- ^ The imported modules.
  , _sCurrentModule :: FullyQName
    -- ^ The current module, fully qualified.
  , _sLocalNames :: LocalNames
    -- ^ The definitions defined so far in the current module.
  , _sAutoImportModules :: AutoImportModules
    -- ^ The list of auto-import modules for the current module.
  }

makeLenses ''Scope

data ScopeError = ScopeError SrcLoc String

instance Show ScopeError where
  show (ScopeError pos err) = show pos ++ ": " ++ err

initScope :: FullyQName -> Scope
initScope n = Scope Set.empty Map.empty Set.empty n Map.empty Set.empty

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

bindLocalName
  :: Name -> NameInfo -> CCheck QName
bindLocalName n ni ret = do
  shadowing <- isJust . Map.lookup n <$> L.view sLocalNames
  when shadowing $
    scopeError n $ "Cannot shadow " ++ render n
  qn <- qualifyName n
  local (over sLocalNames (Map.insert n ni)) $ ret qn

bindDef :: Name -> Hiding -> CCheck QName
bindDef n hidden = bindLocalName n $ DefName hidden

bindVar :: Name -> CCheck Name
bindVar n ret = do
  local (over sVars (Set.insert (nameString n))) $ ret n

bindCon :: Name -> Hiding -> NumberOfArguments -> CCheck QName
bindCon n hidden args = bindLocalName n $ ConName hidden args

bindProj :: Name -> Hiding -> CCheck QName
bindProj n hidden = bindLocalName n $ ProjName hidden

qualifyName :: Name -> Check FullyQName
qualifyName n = (`qNameSnoc` n) <$> L.view sCurrentModule

-- | Resolves a local 'DefName'.  Throws 'scopeError' if not in scope.
resolveLocalDef :: C.Name -> Check (QName, Hiding)
resolveLocalDef cn = do
  let n = mkName cn
  qn <- qualifyName n
  mbNi <- Map.lookup n <$> L.view sLocalNames
  case mbNi of
    Nothing -> scopeError cn $ C.printTree cn ++ " not in scope."
    Just (DefName hidden) -> return (qn, hidden)
    Just _ -> scopeError cn $ C.printTree cn ++ " should be a definition."

-- | Resolves a module.  Throws a 'scopeError' if not in scope.
resolveModule :: QName -> Check (QName, Hiding, LocalNames, AutoImportModules)
resolveModule qn = do
  nameOrDef <- resolveQName qn
  case nameOrDef of
    Right (m, ModuleName hidden names mods) -> return (m, hidden, names, mods)
    _ -> scopeError qn $ render qn ++ " is not a module"

resolveQName :: QName -> Check (Either Name (QName, NameInfo))
resolveQName qn = do
  mb <- lookupQName qn
  case mb of
    Nothing -> scopeError qn $ render qn ++ " not in scope."
    Just x  -> return x

resolveCon :: QName -> Check (Hiding, NumberOfArguments)
resolveCon qn = do
  nameOrDef <- resolveQName qn
  case nameOrDef of
    Right (_, ConName hidden args) -> return (hidden, args)
    _ -> scopeError qn $ render qn ++ " is not a constructor"

-- | Returns a 'Name' if it's a var, a 'NameInfo' if it's some defined
-- name.
--
-- How this works:
--
-- * If the name is unqualified, and a variable variable, we return it
--   immediately.  If it's not a variable, we check in the local names.
--   Finally, we check in the opened names.
--
-- * If the name is qualified, we search for the names in two ways:
--
--   * Try to see if the name, fully qualified, is present in some
--     imported module;
--
--   * Check if any prefix of the qualified name is a module that we can
--     use to lookup the rest of the name in.
--
-- The qualified lookup can yield multiple names, in which case we throw
-- an "ambiguous name" error.
lookupQName :: QName -> Check (Maybe (Either Name (QName, NameInfo)))
lookupQName (QName [] name) = do
  let s = nameString name
  isVar <- Set.member s <$> L.view sVars
  if isVar
    then return $ Just $ Left name
    else do
      traceM =<< (render . Map.toList <$> L.view sOpenedNames)
      mbQn1 <- Map.lookup s <$> L.view sOpenedNames
      mbQn2 <- Map.lookup name <$> L.view sLocalNames
      case (mbQn1, mbQn2) of
        (Just _, Just _) -> scopeError name $ "Ambigous name."
        (Nothing, Nothing) -> return Nothing
        (Just [qn], _) -> lookupQName qn
        (Just _, _) -> scopeError name $ "Ambiguous name"
        (Nothing, Just ni) -> do
          qn <- qualifyName name
          return $ Just $ Right (qn, ni)
lookupQName qn@(QName qual@(_:_) name) = do
  -- Pick every possible module
  xs <- fmap catMaybes $ forM (zip (inits qual) (tails qual)) $ \(module0, qual) -> do
    case module0 of
      [] -> do
        return Nothing
      (_:_) -> do
        let module_ = QName (init module0) (last module0)
        current <- L.view sCurrentModule
        imported <- Set.member (current Semi.<> module_) <$> L.view sImportedModules
        if imported
          then do
            (_, _, names, _) <- resolveModule module_
            local (L.set sVars Set.empty . L.set sLocalNames names) $ lookupQName $ QName qual name
          else return Nothing
  case xs of
    [x] -> return $ Just x
    [] -> scopeError qn $ render qn ++ " not in scope"
    _ -> scopeError qn $ "Ambiguous name"

-- | Accepts a list of new bindings to add to the list of opened names.
-- Fails if we'd have to shadow un-shadowable things -- variables and
-- local names.
bindOpenedNames :: [(Name, FullyQName)] -> CCheck_
bindOpenedNames = mapC_ $ \(n, qn) ret -> do
  let s = nameString n
  definedVar <- Set.member s <$> L.view sVars
  definedLocally <- isJust . Map.lookup n <$> L.view sLocalNames
  when (definedVar || definedLocally) $
    scopeError n $ "Cannot shadow name " ++ render n
  alreadyOpened <- fromMaybe [] . Map.lookup s <$> L.view sOpenedNames
  local (over sOpenedNames (Map.insert s (qn : alreadyOpened))) ret

------------------------------------------------------------------------
-- Scope checking

-- | Scope checks a top-level module.
scopeCheckModule :: C.Module -> Either PP.Doc Module
scopeCheckModule (C.Module (C.Name ((l, c), s)) pars ds) =
  case evalCheck (initScope q) (checkModule' q pars ds return) of
    Left err      -> Left $ PP.text $ show err
    Right (x, _)  -> Right x
  where
    q = QName [] $ Name (SrcLoc l c) s

scopeCheckFile :: FilePath -> IO ()
scopeCheckFile fp = do
  s <- readFile fp
  case C.parseModule s of
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
checkModule' qname@(QName _ name) pars ds ret = do
  case isParamDecl pars of
    Just pars -> do
      -- Prepare the scope for scope-checking the module, by resetting
      -- the auto exports/imports, and setting the current module name
      -- appropriately.
      let prepareScope = L.set sCurrentModule qname
                       . L.set sLocalNames Map.empty
                       . L.set sAutoImportModules Set.empty
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
            definitions <- L.view sLocalNames
            let qdefinitions = map (qNameSnoc qname) $ Map.keys definitions
            autoImports <- L.view sAutoImportModules
            return
              ( ModuleName hidden definitions autoImports
              , Module qname tel qdefinitions ds
              )
      bindLocalName name moduleInfo $ \_ -> do
        -- If the module doesn't have parameters, import it immediately,
        -- and add it to the list of auto imports.
        if null pars
          then local (over sAutoImportModules (Set.insert name)) $
                 ret (module_, [mkRawImportDecl (QName [] name)])
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
    C.NoDataBody set -> case isParamDecl pars of
      Nothing -> scopeError x $ "Bad data declaration " ++ C.printTree x
      Just ps -> checkDataOrRecDecl x ps set $ \sig -> do
                   checkDecls ds $ \ds -> do
                     ret (Data sig : ds)
    C.DataBody cs -> case isParamDef pars of
      Nothing -> do
        scopeError x $ "Bad data definition"
      Just xs -> do
        (x, n) <- resolveLocalDef x
        when (n > length xs) $
          scopeError x $ "Too few parameters to " ++ render x ++
                         " (implicit arguments must be explicitly bound here)"
        xs <- checkHiddenNames n xs
        mapC (bindVar . mkName) xs $ \xs -> do
          let t = App (Def x) (map (\x -> Apply (App (Var x) [])) xs)
          mapC (checkConstructor t xs) cs $ \cs -> checkDecls ds $ \ds' ->
            ret (DataDef x xs cs : ds')
  C.Record x pars mbRecBody : ds -> case mbRecBody of
    C.NoRecordBody set -> case isParamDecl pars of
      Nothing -> scopeError x $ "Bad record declaration " ++ C.printTree x
      Just ps -> checkDataOrRecDecl x ps set $ \sig -> do
                   checkDecls ds $ \ds -> do
                     ret (Record sig : ds)
    C.RecordBody con fs -> case isParamDef pars of
      Nothing -> do
        scopeError x $ "Bad record definition"
      Just xs -> do
        (x, n) <- resolveLocalDef x
        when (n > length xs) $
          scopeError x $ "Too few parameters to " ++ show x ++
                         " (implicit arguments must be explicitly bound here)"
        xs <- checkHiddenNames n xs
        mapC (bindVar . mkName) xs $ \xs -> do
          checkFields (getFields fs) $ \fs ->
            bindCon (mkName con) 0 (length fs) $ \con ->
              -- TODO this is wrong: we should only allow instantiation of
              -- locally defined functions, not all.
              checkDecls ds $ \ds' ->
                ret (RecDef x xs con fs : ds')
  C.FunDef f _ _ _ : _ -> do
    (clauses, ds) <- return $ takeFunDefs f ds
    (f, n) <- resolveLocalDef f
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
    checkModule module_ $ \(module_, mds) -> do
      checkDecls (mds ++ ds) $ \ds -> do
        ret (Module_ module_ : ds)
  C.Import imp : ds -> do
    let (m, args) = case imp of
          C.ImportNoArgs m    -> (mkQName m, [])
          C.ImportArgs m args -> (mkQName m, args)
    (m, hidden, _, autoImports) <- resolveModule m
    args <- insertImplicit (srcLoc m) hidden args
    args <- mapM checkExpr args
    -- Add the import statements for the auto-import modules.
    let importDecls = map (mkRawImportDecl . qNameSnoc m) $ Set.toList autoImports
    -- Add the module to the set of imported modules
    local (over sImportedModules (Set.insert m)) $ do
      checkDecls (importDecls ++ ds) $ \ds -> do
        ret (Import m args : ds)
  C.Open m0 : ds -> do
    let m = mkQName m0
    traceM ("C.Open")
    traceM (render m)
    (m, _, exports, _) <- resolveModule m
    traceM (render m)
    imported <- Set.member m <$> L.view sImportedModules
    -- The module must be imported
    when imported $
      scopeError m $ "To open a module you must import it first"
    -- Add the names -- unqualified -- to the opened stuff
    let opened = [(n, qNameSnoc m n) | (n, _) <- Map.toList exports]
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
  let qname = qNameSnoc f (Name (srcLoc f) (show ix))
  (importedModules, openedNames, ds) <- local (L.set sCurrentModule qname) $ do
    checkDecls ds $ \ds -> do
      (,,) <$> L.view sImportedModules <*> L.view sOpenedNames <*> pure ds
  local (L.set sImportedModules importedModules . L.set sOpenedNames openedNames) $ ret ds

checkTypeSig :: C.TypeSig -> CCheck TypeSig
checkTypeSig (C.Sig x e) ret = do
  (n, a) <- checkScheme e
  bindDef (mkName x) n $ \x -> ret (Sig x a)

checkFields :: [C.Constr] -> CCheck [TypeSig]
checkFields fs ret = do
  fs <- mapC checkField fs return
  mapC bindField fs ret
  where
    bindField :: (C.Name, Natural, Expr) -> CCheck TypeSig
    bindField (x, n, a) ret = bindProj (mkName x) n $ \x -> ret (Sig x a)

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

checkConstructor :: Expr -> [Name] -> C.Constr -> CCheck TypeSig
checkConstructor d xs (C.Constr c e) ret = do
  (n, a) <- checkScheme e
  args   <- checkConstructorType a d xs
  bindCon (mkName c) n args $ \c -> ret (Sig c a)

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
        (Just (Right (_, ConName{})), _) -> checkCon x [] ret
        (Nothing, C.NotQual n) -> bindVar (mkName n) $ ret. VarP
        (_, _) -> scopeError x $ C.printTree x ++ " not in scope"
    (c, ps) -> checkCon c ps ret
  where
    checkCon c0 ps ret = do
      let c = mkQName c0
      (n, args) <- resolveCon c
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
                doProj x e . map Apply =<< checkArgs e n es (\ _ -> return ())
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
    doProj x (App h es1) es2 = return $ App h (es1 ++ [Proj x] ++ es2)
    doProj x e _ = scopeError x $ "Cannot project " ++ show x ++ " from " ++ show e

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
      varOrName <- resolveQName $ mkQName qn
      case varOrName of
        Left x ->
          return (Other $ Var x, 0)
        Right (x, i) -> case i of
          ProjName n       -> return (IsProj x, n)
          ConName n a      -> return (IsCon x a, n)
          DefName n        -> return (Other $ Def x, n)
          ModuleName _ _ _ -> scopeError x $ "Cannot use module name " ++ render x ++ " in term."
          AmbiguousName{}  -> __IMPOSSIBLE__

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
mkQName (C.NotQual n) = QName [] $ mkName n
mkQName (C.Qual qn n) = case mkQName qn of
  QName m n' -> QName (m ++ [n']) $ mkName n

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
    toRawName (QName ns n) = go $ n : ns
      where
        unMkName (Name (SrcLoc l c) s) = C.Name ((l, c), s)

        go []       = __IMPOSSIBLE__
        go [n]      = C.NotQual $ unMkName n
        go (n : ns) = C.Qual (go ns) $ unMkName n

------------------------------------------------------------------------
--  HasSrcLoc instances

instance HasSrcLoc C.Name where
  srcLoc (C.Name ((l, c), _)) = SrcLoc l c

instance HasSrcLoc C.QName where
  srcLoc (C.Qual n _) = srcLoc n
  srcLoc (C.NotQual n) = srcLoc n

instance HasSrcLoc C.Expr where
  srcLoc e = case e of
    C.Lam (x:_) _ -> srcLoc x
    C.Lam [] _    -> error $ "nullary lambda: " ++ show e
    C.Pi tel _    -> srcLoc tel
    C.Fun a _     -> srcLoc a
    C.Eq x _      -> srcLoc x
    C.App (e:_)   -> srcLoc e
    C.App []      -> error "empty application"
    C.Id x        -> srcLoc x

instance HasSrcLoc C.Arg where
  srcLoc (C.Arg e)  = srcLoc e
  srcLoc (C.HArg e) = srcLoc e

instance HasSrcLoc C.Telescope where
  srcLoc (C.Tel (b : _)) = srcLoc b
  srcLoc tel = error $ "empty telescope: " ++ show tel

instance HasSrcLoc C.Binding where
  srcLoc (C.Bind  (x:_) _) = srcLoc x
  srcLoc (C.HBind (x:_) _) = srcLoc x
  srcLoc b = error $ "binding no names: " ++ show b

instance HasSrcLoc C.TypeSig where
  srcLoc (C.Sig x _) = srcLoc x

instance HasSrcLoc C.Decl where
  srcLoc d = case d of
    C.Postulate (d:_)  -> srcLoc d
    C.Postulate []     -> noSrcLoc
    C.TypeSig x        -> srcLoc x
    C.Data x _ _       -> srcLoc x
    C.Record x _ _     -> srcLoc x
    C.FunDef x _ _ _   -> srcLoc x
    C.Open x           -> srcLoc x
    C.Import x         -> srcLoc x
    C.Module_ x        -> srcLoc x
    C.OpenImport x     -> srcLoc x

instance HasSrcLoc C.Import where
  srcLoc x = case x of
    C.ImportNoArgs x -> srcLoc x
    C.ImportArgs x _ -> srcLoc x

instance HasSrcLoc C.Pattern where
  srcLoc p = case p of
    C.IdP x    -> srcLoc x
    C.AppP p _ -> srcLoc p
    C.HideP p  -> srcLoc p

instance HasSrcLoc C.Module where
  srcLoc (C.Module x _ _) = srcLoc x

instance HasSrcLoc C.Params where
  srcLoc (C.ParamDecl (x : _)) = srcLoc x
  srcLoc (C.ParamDef (x : _)) = srcLoc x
  srcLoc _ = noSrcLoc

instance HasSrcLoc C.HiddenName where
  srcLoc (C.NotHidden n) = srcLoc n
  srcLoc (C.Hidden n) = srcLoc n

instance HasSrcLoc AppHead where
  srcLoc h = case h of
    IsProj x     -> srcLoc x
    IsCon c _    -> srcLoc c
    IsRefl p     -> p
    Other h      -> srcLoc h
    HeadSet p    -> p
    HeadMeta p   -> p

{-
    ( scopeCheckModule
    , Scope(..)
    , NameInfo(..)
    ) where

import Prelude
import Data.Bifunctor (first, second)
import Control.Applicative
import Control.Monad.Reader
import Control.Monad.Error
import qualified Data.Map as Map
import qualified Data.Set as Set

import qualified Syntax.Raw as C
import Syntax.Abstract.Abs
import qualified PrettyPrint                      as PP

data ScopeError = ScopeError SrcLoc String

instance Show ScopeError where
  show (ScopeError pos err) = show pos ++ ": " ++ err

instance Error ScopeError where
  strMsg = ScopeError noSrcLoc

type NameInfos = Map.Map String NameInfo

data Scope = Scope
  { scopeInScope :: NameInfos
    -- ^ The 'NameInfo's in scope.
  , scopeAvailableModules :: Set.Set QName
    -- ^ The modules we have 'import'ed.
  , scopeAutoExports :: NameInfos
    -- ^ The definitions in the module that will be exported
    -- automatically -- if no export list is present.
  , scopeAutoImports :: AutoImports
    -- ^ The list of
  , scopeCurrentModule :: QName
    -- ^ The fully qualified name of the current module.
  } deriving (Show)

-- | A list of modules that should be automatically imported when some
-- other module is.
type AutoImports = Set.Set QName

data NameInfo = VarName Name
              | DefName QName Hiding
              | ConName QName Hiding NumberOfArguments
              | ProjName QName Hiding
              | ModuleName QName Hiding NameInfos AutoImports
              | AmbiguousName [QName]
  deriving (Show)

type Hiding            = Int
type NumberOfArguments = Int

initScope :: QName -> Scope
initScope n = Scope Map.empty Set.empty Map.empty Set.empty n

instance HasSrcLoc NameInfo where
  srcLoc i = case i of
    VarName x     -> srcLoc x
    DefName x _   -> srcLoc x
    ConName x _ _ -> srcLoc x
    ProjName x _  -> srcLoc x
    ModuleName x _ _ _ -> srcLoc x
    AmbiguousName [] -> noSrcLoc
    AmbiguousName (x:_) -> srcLoc x

instance PP.Pretty NameInfo where
  pretty (VarName n)     = PP.pretty n
  pretty (DefName n _)   = PP.pretty n
  pretty (ConName n _ _) = PP.pretty n
  pretty (ProjName n _)  = PP.pretty n
  pretty (ModuleName n _ _ _) = PP.pretty n
  pretty (AmbiguousName xs) = "AmbiguousName" PP.<+> PP.pretty xs

newtype Check a = Check { unCheck :: ReaderT Scope (Either ScopeError) a }
  deriving (Functor, Applicative, Monad, MonadReader Scope, MonadError ScopeError)

evalCheck :: Scope -> Check a -> Either ScopeError a
evalCheck sc m = runReaderT (unCheck m) sc

type CCheck a = forall b. (a -> Check b) -> Check b
type CCheck_ = forall b. Check b -> Check b

mapC :: (a -> CCheck b) -> [a] -> CCheck [b]
mapC _ [] ret = ret []
mapC f (x : xs) ret = f x $ \y -> mapC f xs $ \ys -> ret (y : ys)

concatMapC :: (a -> CCheck [b]) -> [a] -> CCheck [b]
concatMapC f xs ret = mapC f xs $ ret . concat

scopeError :: HasSrcLoc i => i -> String -> Check a
scopeError p err = throwError $ ScopeError (srcLoc p) err

reservedNames = ["_", "Set", "refl", "J"]

impossible err = fail $ "impossible: " ++ err

qualifyName :: Name -> Check QName
qualifyName n = do
  QName ns mn <- asks scopeCurrentModule
  return $ QName (ns ++ [mn]) n

mkName :: C.Name -> Name
mkName (C.Name ((l, c), s)) = Name (SrcLoc l c) s

checkShadowing :: C.Name -> Check ()
checkShadowing n = do
  mb <- resolveName' n
  case mb of
    Nothing -> return ()
    Just ni -> scopeError n $ "Cannot shadow previous definition of " ++ C.printTree n ++
               " at " ++ PP.render (srcLoc ni)

bindVar :: C.Name -> CCheck Name
bindVar cn@(C.Name (_, s)) ret = do
  let n = mkName cn
  bindNameInfos (Map.fromList [(s, VarName n)]) $ ret n

bindDef :: C.Name -> Hiding -> CCheck QName
bindDef cn@(C.Name (_, s)) hi ret = do
  checkShadowing cn
  let n = mkName cn
  qn <- qualifyName n
  bindAndAutoExportNameInfo s (DefName qn hi) $ ret qn

bindCon :: C.Name -> Hiding -> NumberOfArguments -> CCheck QName
bindCon cn@(C.Name (_, s)) hi args ret = do
  checkShadowing cn
  let n = mkName cn
  qn <- qualifyName n
  bindAndAutoExportNameInfo s (ConName qn hi args) $ ret qn

bindProj :: C.Name -> Hiding -> CCheck QName
bindProj cn@(C.Name (_, s)) hi ret = do
  checkShadowing cn
  let n = mkName cn
  qn <- qualifyName n
  bindAndAutoExportNameInfo s (ProjName qn hi) $ ret qn

bindModule :: C.Name -> Hiding -> NameInfos -> AutoImports -> CCheck QName
bindModule cn@(C.Name (_, s)) hi names autoImports ret = do
  checkShadowing cn
  let n = mkName cn
  qn <- qualifyName n
  bindAndAutoExportNameInfo s (ModuleName qn hi names autoImports) $ ret qn

bindAndAutoExportNameInfo :: String -> NameInfo -> CCheck_
bindAndAutoExportNameInfo s ni ret =
  bindNameInfos (Map.fromList [(s, ni)]) $
    local (\sc -> sc{scopeAutoExports = Map.insert s ni (scopeAutoExports sc)}) ret

bindNameInfos :: NameInfos -> CCheck_
bindNameInfos names ret =
  local (\sc -> sc{scopeInScope = Map.unionWith checkAmbiguity (scopeInScope sc) names}) ret
  where
    checkAmbiguity _ ni@VarName{} = ni
    checkAmbiguity VarName{} ni = ni
    checkAmbiguity ni1 ni2 = AmbiguousName $ getQNames ni1 ++ getQNames ni2

    getQNames VarName{} = error "bindNameInfos: impossible"
    getQNames (DefName qn _) = [qn]
    getQNames (ConName qn _ _) = [qn]
    getQNames (ProjName qn _) = [qn]
    getQNames (ModuleName qn _ _ _) = [qn]
    getQNames (AmbiguousName qns) = qns

resolveName' :: C.Name -> Check (Maybe NameInfo)
resolveName' x@(C.Name (_, s))
  | elem s reservedNames = impossible "reserved names should not end up in resolveName"
  | otherwise = checkAmbiguity =<< asks (Map.lookup s . scopeInScope)
  where
    checkAmbiguity (Just (AmbiguousName xs)) = scopeError x $
      C.printTree x ++ " could be any of " ++ PP.render xs
    checkAmbiguity ni =
      return ni

resolveName :: C.Name -> Check NameInfo
resolveName x@(C.Name ((l, c), s)) = do
  mi <- resolveName' x
  case mi of
    Nothing -> scopeError x $ "Not in scope: " ++ C.printTree x
    Just (VarName _)     -> return (VarName y)
    Just (DefName q n)   -> return (DefName q{qNameName = y} n)
    Just (ConName q n a) -> return (ConName q{qNameName = y} n a)
    Just (ProjName q n)  -> return (ProjName q{qNameName = y} n)
    Just (ModuleName q n ns ae) -> return (ModuleName q{qNameName = y} n ns ae)
    Just (AmbiguousName _) -> error "resolveName: impossible"
  where
    y = Name (SrcLoc l c) s

resolveQName :: C.QName -> Check NameInfo
resolveQName (C.NotQual n) = do
  resolveName n
resolveQName (C.Qual ns n) = do
  (_, _, names, _) <- resolveModule_ ns
  local (\sc -> sc{scopeInScope = names}) $ resolveName n

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

telHiding :: [C.Binding] -> (Hiding, [C.Binding], Bool)
telHiding [] = (0, [], False)
telHiding bs@(C.Bind{} : _) = (0, bs, True)
telHiding (C.HBind xs e : bs0) =
  let (n, bs, stop) = telHiding bs0
  in (n + length xs, C.Bind xs e : bs, stop)

-- | Scope checks a top-level module.
scopeCheckModule :: C.Module -> Either PP.Doc Module
scopeCheckModule module_@(C.Module (C.Name ((l, c), s)) _ _) =
  case evalCheck (initScope q) (checkModule module_ return) of
    Left err      -> Left $ PP.text $ show err
    Right (x, _)  -> Right x
  where
    q = QName [] $ Name (SrcLoc l c) s


isSet :: C.Name -> Check ()
isSet (C.Name (_, "Set")) = return ()
isSet e = scopeError e "The type of a datatype or record should be Set"

resolveDef :: C.Name -> Check (QName, Hiding)
resolveDef x = do
  i <- resolveName x
  case i of
    DefName x n -> return (x, n)
    _ -> scopeError x $ show x ++ " should be a defined name."

resolveCon :: C.Name -> Check (QName, Hiding, NumberOfArguments)
resolveCon x = do
  i <- resolveName x
  case i of
    ConName c n args -> return (c, n, args)
    _                -> scopeError x $ C.printTree x ++ " should be a constructor"

resolveModule :: C.QName -> Check (Maybe (QName, Hiding, NameInfos, AutoImports))
resolveModule qn = do
  i <- resolveQName qn
  case i of
    ModuleName qn n ns ai -> do
      return $ Just (qn, n, ns, ai)
    DefName _ _ -> do
      return Nothing -- TODO fix this when we have record-modules
    _ -> do
      scopeError qn $ C.printTree qn ++ " should be a module"

resolveModule_ :: C.QName -> Check (QName, Hiding, NameInfos, AutoImports)
resolveModule_ qn = do
  mb <- resolveModule qn
  case mb of
    Just x -> return x
    Nothing -> error "resolveModule_: impossible"

isModuleImported :: QName -> Check Bool
isModuleImported moduleName = asks $ Set.member moduleName . scopeAvailableModules

resolveImportedModule :: C.QName -> Check (Maybe (QName, Hiding, NameInfos, AutoImports))
resolveImportedModule qn = do
  mb <- resolveModule qn
  case mb of
    Nothing -> return Nothing
    Just res@(moduleName, _, _, _) -> do
      imported <- isModuleImported moduleName
      unless imported $
        scopeError qn $ PP.render qn ++ " should be imported."
      return $ Just res

checkHiddenNames :: Hiding -> [C.HiddenName] -> Check [C.Name]
checkHiddenNames 0 (C.NotHidden x : xs) = (x :) <$> checkHiddenNames 0 xs
checkHiddenNames _ (C.NotHidden x : _)  = scopeError x $ "Expected implicit binding of " ++ C.printTree x
checkHiddenNames 0 (C.Hidden x : _)     = scopeError x $ "Expected explicit binding of " ++ C.printTree x
checkHiddenNames n (C.Hidden x : xs)    = (x :) <$> checkHiddenNames (n - 1) xs
checkHiddenNames 0 []                   = return []
checkHiddenNames _ []                   = impossible "checkHiddenNames _ []"

isParamDecl :: C.Params -> Maybe [C.Binding]
isParamDecl C.NoParams       = Just []
isParamDecl (C.ParamDecl ps) = Just ps
isParamDecl C.ParamDef{}     = Nothing

isParamDef :: C.Params -> Maybe [C.HiddenName]
isParamDef C.NoParams      = Just []
isParamDef C.ParamDecl{}   = Nothing
isParamDef (C.ParamDef xs) = Just xs

enableModule :: QName -> CCheck_
enableModule moduleName ret = do
  availableModules <- asks scopeAvailableModules
  when (Set.member moduleName availableModules) $
    scopeError moduleName $ "Cannot import module " ++ PP.render moduleName ++
                            " twice."
  local (\sc -> sc{scopeAvailableModules = Set.insert moduleName availableModules}) ret

moduleNames :: Check ([QName], NameInfos)
moduleNames = do
  nameInfos <- asks scopeAutoExports
  return (map getQualifiedName (Map.elems nameInfos), nameInfos)
  where
    getQualifiedName (VarName _) = error "Got VarName in `moduleNames'"
    getQualifiedName (DefName n _) = n
    getQualifiedName (ConName n _ _) = n
    getQualifiedName (ProjName n _) = n
    getQualifiedName (ModuleName n _ _) = n
    getQualifiedName (AmbiguousName _) = error "Got AmbiguousName in `moduleNames'"

checkDecls :: [C.Decl] -> CCheck [Decl]
checkDecls ds0 ret = case ds0 of
  [] ->
    ret []
  C.Postulate [] : ds ->
    checkDecls ds ret
  C.Postulate (sig0 : sigs) : ds ->
    checkTypeSig sig0 $ \sig -> checkDecls (C.Postulate sigs : ds) $ \ds' ->
      ret (Postulate sig : ds')
  C.TypeSig sig0 : ds -> do
    checkTypeSig sig0 $ \sig -> checkDecls ds $ \ds' ->
      ret (TypeSig sig : ds')
  C.Data x pars (C.NoDataBody set) : ds | Just ps <- isParamDecl pars -> do
    dataDecl x ps set ds
  C.Record x pars (C.NoRecordBody set) : ds | Just ps <- isParamDecl pars -> do
    recDecl x ps set ds
  C.Data x pars (C.DataBody cs) : ds | Just xs <- isParamDef pars -> do
    (x, n) <- resolveDef x
    when (n > length xs) $ scopeError x $ "Too few parameters to " ++ show x ++
                                          " (implicit arguments must be explicitly bound here)"
    xs <- checkHiddenNames n xs
    mapC bindVar xs $ \xs -> do
      let t = App (Def x) (map (\x -> Apply (App (Var x) [])) xs)
      mapC (checkConstructor t xs) cs $ \cs -> checkDecls ds $ \ds' ->
        ret (DataDef x xs cs : ds')
  C.Record x pars (C.RecordBody con fs) : ds | Just xs <- isParamDef pars -> do
    (x, n) <- resolveDef x
    when (n > length xs) $ scopeError x $ "Too few parameters to " ++ show x ++
                                          " (implicit arguments must be explicitly bound here)"
    xs <- checkHiddenNames n xs
    mapC bindVar xs $ \xs -> do
      checkFields (getFields fs) $ \fs ->
        bindCon con 0 (length fs) $ \con ->
          -- TODO this is wrong: we should only allow instantiation of
          -- locally defined functions, not all.
          checkDecls ds $ \ds' ->
            ret (RecDef x xs con fs : ds')
  (d@C.Data{} : _) ->
    scopeError d $ "Bad data declaration"
  (d@C.Record{} : _) ->
    scopeError d $ "Bad record declaration"
  C.FunDef f _ _ _ : _ -> do
    let (clauses, ds) = takeFunDefs f ds0
    (f, n) <- resolveDef f
    clauses <- forM clauses $ \(ps, b, wheres0) -> do
      let wheres = case wheres0 of
            C.Where ds -> ds
            C.NoWhere -> []
      ps <- insertImplicitPatterns (srcLoc f) n ps
      mapC checkPattern ps $ \ps -> do
        checkDecls wheres $ \wheres -> do
          b <- checkExpr b
          return $ Clause ps b wheres
    checkDecls ds $ \ds' -> ret (FunDef f clauses : ds')
  C.Import imp : ds -> do
    let (x, args) = case imp of
          C.ImportNoArgs x    -> (x, [])
          C.ImportArgs x args -> (x, args)
    mbM <- resolveModule x
    case mbM of
      Just (moduleName, n, _) -> do
        imported <- isModuleImported moduleName
        when imported $
          scopeError imp $ "Module " ++ PP.pretty moduleName ++ " is already imported."
        args <- insertImplicit (srcLoc moduleName) n args
        args <- mapM checkExpr args
        enableModule moduleName $
          checkDecls ds $ \ds' -> ret (Import moduleName args : ds')
      Nothing ->
        -- TODO fix when we implement record as modules
        checkDecls ds ret
  C.Open x : ds -> do
    mbM <- resolveImportedModule x
    case mbM of
      Just (moduleName, _, exportedNames) -> do
        bindNameInfos exportedNames $ \_ -> checkDecls ds $ \ds' ->
          ret (Open moduleName : ds')
      Nothing -> do
        -- TODO fix when we implement record as modules
        checkDecls ds ret
  C.OpenImport imp : ds -> do
    let x = case imp of
          C.ImportNoArgs x -> x
          C.ImportArgs x _ -> x
    checkDecls (C.Import imp : C.Open x : ds) ret
  C.Module_ module_ : ds -> do
    checkModule module_ $ \(module_, moduleDs) ->
      checkDecls ds $ \ds' -> ret (Module_ module_ : moduleDs ++ ds')
  where
    dataDecl = dataOrRecDecl Data
    recDecl = dataOrRecDecl Record

    dataOrRecDecl f x ps set ds = do
      isSet set
      (n, a) <- checkScheme (C.Pi (C.Tel ps) (C.App [C.Arg $ C.Id $ C.NotQual set]))
      bindDef x n $ \x -> checkDecls ds $ \ds' ->
        ret (f (Sig x a) : ds')

    takeFunDefs :: C.Name -> [C.Decl] -> ([([C.Pattern], C.Expr, C.Where)], [C.Decl])
    takeFunDefs _ [] =
      ([], [])
    takeFunDefs f (C.FunDef f' ps b wheres : ds) | sameName f f' =
      first ((ps, b, wheres) :) $ takeFunDefs f ds
    takeFunDefs _ d =
      ([], d)

    sameName (C.Name (_, f1)) (C.Name (_, f2)) = f1 == f2

checkModule :: C.Module -> CCheck (Module, [Decl])
checkModule (C.Module moduleName pars ds) ret = do
  qModuleName <- qualifyName $ mkName moduleName
  case isParamDecl pars of
    Just ps0 -> do
      (module_, n, names) <-
        local (\s -> s{scopeCurrentModule = qModuleName, scopeAutoExports = Map.empty, scopeAutoImports = Set.empty}) $ do
          let (n, ps, _) = telHiding ps0
          checkTel ps $ \tel -> do
            checkDecls ds $ \ds' -> do
              (names, nameInfos) <- moduleNames
              ai <- asks scopeAutoImports
              return (Module qModuleName tel names ds', n, nameInfos)
      bindModule moduleName n names $ \_ -> do
        -- If the module doesn't have parameters, import it immediately,
        -- and add it to the list of auto imports.
        let decls = if null ps0 then [Import qModuleName []] else []
        ret (module_, decls)
    Nothing ->
      scopeError pars "Bad module declaration"

checkTypeSig :: C.TypeSig -> CCheck TypeSig
checkTypeSig (C.Sig x e) ret = do
  (n, a) <- checkScheme e
  bindDef x n $ \x -> ret (Sig x a)

checkFields :: [C.Constr] -> CCheck [TypeSig]
checkFields fs ret = do
  fs <- mapC checkField fs return
  mapC bindField fs ret
  where
    bindField :: (C.Name, Int, Expr) -> CCheck TypeSig
    bindField (x, n, a) ret = bindProj x n $ \x -> ret (Sig x a)

checkField :: C.Constr -> CCheck (C.Name, Int, Expr)
checkField (C.Constr c e) ret = do
  (n, a) <- checkScheme e
  bindVar c $ \_ -> ret (c, n, a)

getFields :: C.Fields -> [C.Constr]
getFields C.NoFields    = []
getFields (C.Fields fs) = fs

checkConstructor :: Expr -> [Name] -> C.Constr -> CCheck TypeSig
checkConstructor d xs (C.Constr c e) ret = do
  (n, a) <- checkScheme e
  args   <- checkConstructorType a d xs
  bindCon c n args $ \c -> ret (Sig c a)

checkScheme :: C.Expr -> Check (Hiding, Expr)
checkScheme e = do
  (n, e) <- checkHiding e
  a      <- checkExpr e
  return (n, a)

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

cMeta :: HasSrcLoc a => a -> C.Expr
cMeta x = C.App [C.Arg $ C.Id $ C.NotQual $ C.Name ((l, c), "_")]
  where SrcLoc l c = srcLoc x

cWild :: HasSrcLoc a => a -> C.Pattern
cWild x = C.IdP (C.Name ((l, c), "_"))
  where SrcLoc l c = srcLoc x

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

type PAppView = (C.Name,  [C.Pattern])

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
    (C.Name ((l, c), "_"), []) -> ret $ WildP (SrcLoc l c)
    (x, []) -> do
      mi <- resolveName' x
      case mi of
        Just ConName{} -> checkCon x [] ret
        _              -> bindVar x $ ret . VarP
    (c, ps) -> checkCon c ps ret
  where
    checkCon c ps ret = do
      (c, n, args) <- resolveCon c
      ps <- insertImplicitPatterns (srcLoc c) n ps
      checkNumberOfConstructorArguments p c ps args
      mapC checkPattern ps $ \ps -> ret (ConP c ps)

checkExpr :: C.Expr -> Check Expr
checkExpr e = case e of
  C.Pi (C.Tel tel) b ->
    checkTel tel $ \tel -> do
      b <- checkExpr b
      return $ foldr (uncurry Pi) b tel
  C.Fun a b -> Fun <$> checkExpr a <*> checkExpr b
  C.Lam xs e ->
    mapC bindVar xs $ \xs ->
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
                doProj x e . map Apply =<< checkArgs e n es (\ _ -> return ())
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
    doProj x (App h es1) es2 = return $ App h (es1 ++ [Proj x] ++ es2)
    doProj x e _ = scopeError x $ "Cannot project " ++ show x ++ " from " ++ show e

checkArgs :: HasSrcLoc a =>
             a -> Hiding -> [C.Arg] -> (forall b. [b] -> Check ()) ->
             Check [Expr]
checkArgs x n es extraCheck = do
  es <- insertImplicit (srcLoc x) n es
  extraCheck es
  mapM checkExpr es

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

data AppHead = IsProj QName
             | IsCon QName NumberOfArguments
             | IsRefl SrcLoc
             | Other Head
             | HeadSet SrcLoc
             | HeadMeta SrcLoc

instance HasSrcLoc AppHead where
  srcLoc h = case h of
    IsProj x     -> srcLoc x
    IsCon c _    -> srcLoc c
    IsRefl p     -> p
    Other h      -> srcLoc h
    HeadSet p    -> p
    HeadMeta p   -> p

data AppView = CApp C.QName [C.Arg]
             | NotApp C.Expr

appView :: C.Expr -> Check AppView
appView e = case e of
  C.App (arg@C.HArg{} : _) ->
    scopeError arg $ "Unexpected curly braces: " ++ C.printTree arg
  C.App (C.Arg e : es) -> applyTo es =<< appView e
  C.App []             -> impossible "appView: empty application"
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
      i <- resolveQName qn
      case i of
        ProjName x n     -> return (IsProj x, n)
        VarName x        -> return (Other $ Var x, 0)
        ConName x n a    -> return (IsCon x a, n)
        DefName x n      -> return (Other $ Def x, n)
        ModuleName x _ _ -> scopeError x $ "Cannot use module name " ++ PP.render x ++ " in term."
        AmbiguousName _  -> error "checkAppHead: impossible"

checkTel :: [C.Binding] -> CCheck Params
checkTel = concatMapC checkBinding

checkBinding :: C.Binding -> CCheck [(Name, Expr)]
checkBinding b@C.HBind{} _ = scopeError b $ "Implicit binding must be on top level: " ++ C.printTree b
checkBinding (C.Bind args e) ret = do
  xs <- mapM argName args
  a <- checkExpr e
  mapC bindVar xs $ \ys -> ret [ (y, a) | y <- ys ]

argName :: C.Arg -> Check C.Name
argName (C.Arg (C.Id (C.NotQual x))) = return x
argName a = scopeError a $ "Expected variable name: " ++ C.printTree a

-- SrcLoc instances --

instance HasSrcLoc C.Name where
  srcLoc (C.Name ((l, c), _)) = SrcLoc l c

instance HasSrcLoc C.QName where
  srcLoc (C.Qual n _) = srcLoc n
  srcLoc (C.NotQual n) = srcLoc n

instance HasSrcLoc C.Expr where
  srcLoc e = case e of
    C.Lam (x:_) _ -> srcLoc x
    C.Lam [] _    -> error $ "nullary lambda: " ++ show e
    C.Pi tel _    -> srcLoc tel
    C.Fun a _     -> srcLoc a
    C.Eq x _      -> srcLoc x
    C.App (e:_)   -> srcLoc e
    C.App []      -> error "empty application"
    C.Id x        -> srcLoc x

instance HasSrcLoc C.Arg where
  srcLoc (C.Arg e)  = srcLoc e
  srcLoc (C.HArg e) = srcLoc e

instance HasSrcLoc C.Telescope where
  srcLoc (C.Tel (b : _)) = srcLoc b
  srcLoc tel = error $ "empty telescope: " ++ show tel

instance HasSrcLoc C.Binding where
  srcLoc (C.Bind  (x:_) _) = srcLoc x
  srcLoc (C.HBind (x:_) _) = srcLoc x
  srcLoc b = error $ "binding no names: " ++ show b

instance HasSrcLoc C.TypeSig where
  srcLoc (C.Sig x _) = srcLoc x

instance HasSrcLoc C.Decl where
  srcLoc d = case d of
    C.Postulate (d:_)  -> srcLoc d
    C.Postulate []     -> noSrcLoc
    C.TypeSig x        -> srcLoc x
    C.Data x _ _       -> srcLoc x
    C.Record x _ _     -> srcLoc x
    C.FunDef x _ _ _   -> srcLoc x
    C.Open x           -> srcLoc x
    C.Import x         -> srcLoc x
    C.Module_ x        -> srcLoc x
    C.OpenImport x     -> srcLoc x

instance HasSrcLoc C.Import where
  srcLoc x = case x of
    C.ImportNoArgs x -> srcLoc x
    C.ImportArgs x _ -> srcLoc x

instance HasSrcLoc C.Pattern where
  srcLoc p = case p of
    C.IdP x    -> srcLoc x
    C.AppP p _ -> srcLoc p
    C.HideP p  -> srcLoc p

instance HasSrcLoc C.Module where
  srcLoc (C.Module x _ _) = srcLoc x

instance HasSrcLoc C.Params where
  srcLoc (C.ParamDecl (x : _)) = srcLoc x
  srcLoc (C.ParamDef (x : _)) = srcLoc x
  srcLoc _ = noSrcLoc

instance HasSrcLoc C.HiddenName where
  srcLoc (C.NotHidden n) = srcLoc n
  srcLoc (C.Hidden n) = srcLoc n
-}
