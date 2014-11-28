-- {-# OPTIONS_GHC -fwarn-incomplete-patterns -Werror #-}
module Syntax.Abstract.Scope
    ( scopeCheckProgram
    , scopeCheckExpr
    , Scope(..)
    , NameInfo(..)
    ) where

-- Is there a real need to use this rankNType continuation passing style

import Prelude
import Control.Arrow (first, second)
import Control.Applicative
import Control.Monad.Reader
import Control.Monad.Writer -- rewrite to use this instead
import Control.Monad.Error
import Data.Monoid -- implement instance for the Scope and the Check type (presumably)
import qualified Data.Map as Map
import Data.Map (Map)

import qualified Syntax.Raw as C
import Syntax.Abstract.Abs
import qualified PrettyPrint                      as PP

data ScopeError = ScopeError SrcLoc String

instance Show ScopeError where
  show (ScopeError pos err) = show pos ++ ": " ++ err

instance Error ScopeError where
  strMsg = ScopeError noSrcLoc

data Scope = Scope
  { inScope :: Map String NameInfo
  }

updateScope :: (Map String NameInfo -> Map String NameInfo) -> Scope -> Scope
updateScope f s = s { inScope = f (inScope s) }

initScope :: Scope
initScope = Scope $ Map.fromList []

type Hiding            = Int
type NumberOfArguments = Int

data NameInfo = VarName Name
              | DefName Name Hiding
              | ConName Name Hiding NumberOfArguments
              | ProjName Name Hiding

infoName :: NameInfo -> Name
infoName (VarName x)     = x
infoName (DefName x _)   = x
infoName (ConName x _ _) = x
infoName (ProjName x _)  = x

infoStringName :: NameInfo -> String
infoStringName i = s
  where Name _ s = infoName i

infoHiding :: NameInfo -> Hiding
infoHiding (VarName _)     = 0
infoHiding (DefName _ n)   = n
infoHiding (ConName _ n _) = n
infoHiding (ProjName _ n)  = n

instance HasSrcLoc NameInfo where
  srcLoc i = case i of
    VarName x     -> srcLoc x
    DefName x _   -> srcLoc x
    ConName x _ _ -> srcLoc x
    ProjName x _  -> srcLoc x

newtype Check a = Check { unCheck :: ReaderT Scope (Either ScopeError) a }
  deriving (Functor, Applicative, Monad, MonadReader Scope, MonadError ScopeError)

type CCheck a = forall b. (a -> Check b) -> Check b

mapC :: (a -> CCheck b) -> [a] -> CCheck [b]
mapC _ []       ret = ret []
mapC f (x : xs) ret = f x $ \ y -> mapC f xs $ \ ys -> ret (y : ys)
  -- cf. f x >>= \ y -> mapM f xs >>= \ ys -> return (y : ys)

concatMapC :: (a -> CCheck [b]) -> [a] -> CCheck [b]
concatMapC f xs ret = mapC f xs $ \ ys -> ret (concat ys)

scopeError :: HasSrcLoc i => i -> String -> Check a
scopeError p err = throwError $ ScopeError (srcLoc p) err

reservedNames :: [String]
reservedNames = ["_", "Set", "refl", "J"]

impossible :: Monad m => String -> m a
impossible err = fail $ "impossible: " ++ err

mkName :: Int -> Int -> String -> Name
mkName l c s = Name (SrcLoc l c) s

fromCName :: C.Name -> Name
fromCName (C.Name ((l, c), s)) = mkName l c s


mkVarInfo :: C.Name -> NameInfo
mkVarInfo = VarName . fromCName

mkDefInfo :: C.Name -> Hiding -> NameInfo
mkDefInfo = DefName . fromCName

mkConInfo :: C.Name -> Hiding -> NumberOfArguments -> NameInfo
mkConInfo = ConName . fromCName

mkProjInfo :: C.Name -> Hiding -> NameInfo
mkProjInfo = ProjName . fromCName


resolveName'' :: C.Name -> Check (Maybe NameInfo)
resolveName'' (C.Name (_, s))
  | s `elem` reservedNames = impossible "reserved names should not end up in resolveName"
  | otherwise = Map.lookup s <$> asks inScope

resolveName' :: C.Name -> Check NameInfo
resolveName' x@(C.Name ((l, c), s)) = do
  mi <- resolveName'' x
  case mi of
    Nothing -> scopeError x $ "Not in scope: " ++ C.printTree x
    Just (VarName _)     -> return (VarName y)
    Just (DefName _ n)   -> return (DefName y n)
    Just (ConName _ n a) -> return (ConName y n a)
    Just (ProjName _ n)  -> return (ProjName y n)
  where
    y = Name (SrcLoc l c) s

checkShadowing :: NameInfo -> Maybe NameInfo -> Check ()
checkShadowing _ Nothing   = return ()
checkShadowing VarName{} _ = return ()
checkShadowing i (Just j)  =
  scopeError i $ "Cannot shadow previous definition of " ++ infoStringName j ++
                 " at " ++ show (srcLoc j)

bindName :: NameInfo -> CCheck Name
bindName i ret = do
  checkShadowing i =<< Map.lookup s <$> asks inScope
  local (updateScope $ Map.insert s i) $ ret x
  where
    s = infoStringName i
    x = infoName i

-- checkHiding :: C.Expr -> Check (Hiding, C.Expr)
-- checkHiding e = case e of
--   C.Fun a b  -> second (C.Fun a) <$> checkHiding b
--   C.Pi (C.Tel tel) b -> do
--     (n, tel, stop) <- telHiding tel
--     if stop then return (n, C.Pi (C.Tel tel) b)
--             else do
--       (m, b) <- checkHiding b
--       return (n + m, C.Pi (C.Tel tel) b)
--   _ -> return (0, e)
--   where
--     telHiding [] = return (0, [], False)
--     telHiding bs@(C.Bind{} : _) = return (0, bs, True)
--     telHiding (C.HBind xs e : bs) = do
--       (n, bs, stop) <- telHiding bs
--       return (n + length xs, C.Bind xs e : bs, stop)

{- Counts number of hidden args up until the first explicit,
at the same time turning them into explicits. Does not assert that
the following args are only explicits though, so no "check" is really done.
Only searches for implicits at top-level, since they're only allowed there,
as checked by checkBinding.

Not sure if we want to retain behaviour of turning every implicit into explicit,
and how it interplays with PiImpls.

TODO: Extend and rewrite so it also creates PiImpls when that is possible.
-}
countFirstHidden :: C.Expr -> (Hiding, C.Expr)
countFirstHidden e = case e of 
    C.Fun dom cod        -> second (C.Fun dom) $ countFirstHidden cod
    C.Pi (C.Tel tel) cod -> let pi' = C.Pi (C.Tel tel') in
      if stop then (n    , pi' cod)
              else (n + m, pi' cod')
      where
        (n, tel', stop) = hiddenInTel tel
        (m, cod')       = countFirstHidden cod
    _                    -> (0,e)
  where
    hiddenInTel []                  = (0, [], False)
    hiddenInTel bs@(C.Bind{} : _)   = (0, bs, True)
    hiddenInTel (C.HBind xs e : bs) = let (n, bs', stop) = hiddenInTel bs in
      (length xs + n, C.Bind xs e : bs', stop)

scopeCheckProgram :: C.Program -> Either PP.Doc Program
scopeCheckProgram (C.Prog _ ds) =
  case runReaderT (unCheck (checkDecls ds return)) initScope of
    Left err -> Left $ PP.text $ show err
    Right x  -> Right x

scopeCheckExpr :: Scope -> C.Expr -> Either PP.Doc Expr
scopeCheckExpr s e =
  case runReaderT (unCheck (checkExpr e)) s of
    Left err -> Left $ PP.text $ show err
    Right x  -> Right x

isSet :: C.Name -> Check ()
isSet (C.Name ((l, c), "Set")) = return ()
isSet e = scopeError e "The type of a datatype or record should be Set"

resolveDef :: C.Name -> Check (Name, Hiding)
resolveDef x = do
  i <- resolveName' x
  case i of
    DefName x n -> return (x, n)
    _ -> scopeError x $ show x ++ " should be a defined name."

resolveCon :: C.Name -> Check (Name, Hiding, NumberOfArguments)
resolveCon x = do
  i <- resolveName' x
  case i of
    ConName c n args -> return (c, n, args)
    _                -> scopeError x $ C.printTree x ++ " should be a constructor"

checkHiddenNames :: Hiding -> [C.HiddenName] -> Check [C.Name]
checkHiddenNames 0 (C.NotHidden x : xs) = (x :) <$> checkHiddenNames 0 xs
checkHiddenNames n (C.NotHidden x : _)  = scopeError x $ "Expected implicit binding of " ++ C.printTree x
checkHiddenNames 0 (C.Hidden x : _)     = scopeError x $ "Expected explicit binding of " ++ C.printTree x
checkHiddenNames n (C.Hidden x : xs)    = (x :) <$> checkHiddenNames (n - 1) xs
checkHiddenNames 0 []                   = return []
checkHiddenNames _ []                   = impossible "checkHiddenNames _ []"


{- Checks if parameter structure corresponds to a data/rec *declaration*, e.g.

data Vec (A : Set) (n : Nat) : Set

i.e., parameters should be list of bindings.
-}
isParamDecl :: C.Params -> Maybe [C.Binding]
isParamDecl C.NoParams       = Just []
isParamDecl (C.ParamDecl ps) = Just ps
isParamDecl C.ParamDef{}     = Nothing


{- Checks if parameter structure corresponds to a data/rec *definition*, eg.

data Vec A n where
  ...

i.e., parameters should be list of (possibly hidden) names.
-}
isParamDef :: C.Params -> Maybe [C.HiddenName]
isParamDef C.NoParams      = Just []
isParamDef C.ParamDecl{}   = Nothing
isParamDef (C.ParamDef xs) = Just xs


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
    let is = map mkVarInfo xs
    xs <- mapC bindName is $ return
    let t = App (Def x) $ map (eapply . var) xs
    mapC (checkConstructor t is) cs $ \cs -> checkDecls ds $ \ds' ->
      ret (DataDef x xs cs : ds')
  C.Record x pars (C.RecordBody con fs) : ds | Just xs <- isParamDef pars -> do
    (x, n) <- resolveDef x
    when (n > length xs) $ scopeError x $ "Too few parameters to " ++ show x ++
                                          " (implicit arguments must be explicitly bound here)"
    xs <- checkHiddenNames n xs
    let is = map mkVarInfo xs
    xs <- mapC bindName is $ return
    checkFields is (getFields fs) $ \fs ->
      bindName (mkConInfo con 0 (length fs)) $ \con ->
        -- TODO this is wrong: we should only allow instantiation of
        -- locally defined functions, not all.
        checkDecls ds $ \ds' ->
          ret (RecDef x xs con fs : ds')
  (d@C.Data{} : _) ->
    scopeError d "Bad data declaration"
  (d@C.Record{} : _) ->
    scopeError d "Bad record declaration"
  C.FunDef f _ _ _ : _ -> do
    let (clauses, ds) = takeFunDefs f ds0
    (f, n) <- resolveDef f
    clauses <- forM clauses $ \(ps, b, wheres) -> do
      case wheres of
        C.Where _ ->
          error "checkScope: TODO where clauses"
        C.NoWhere -> do
          ps <- insertImplicitPatterns (srcLoc f) n ps
          mapC checkPattern ps $ \ps -> do
            b <- checkExpr b
            return $ Clause ps b
    checkDecls ds $ \ds' -> ret (FunDef f clauses : ds')
  C.Open x : ds -> do
    resolveDef x
    checkDecls ds ret
  C.Import{} : ds -> do
    checkDecls ds ret
  where
    dataDecl = dataOrRecDecl Data
    recDecl = dataOrRecDecl Record

    dataOrRecDecl f x ps set ds = do
      isSet set
      (n, a) <- checkScheme (C.Pi (C.Tel ps) (C.App [C.Arg $ C.Id set]))
      bindName (mkDefInfo x n) $ \x -> checkDecls ds $ \ds' ->
        ret (f (Sig x a) : ds')

    takeFunDefs :: C.Name -> [C.Decl] -> ([([C.Pattern], C.Expr, C.Where)], [C.Decl])
    takeFunDefs f [] =
      ([], [])
    takeFunDefs f (C.FunDef f' ps b wheres : ds) | sameName f f' =
      first ((ps, b, wheres) :) $ takeFunDefs f ds
    takeFunDefs _ d =
      ([], d)

    sameName (C.Name (_, f1)) (C.Name (_, f2)) = f1 == f2

checkTypeSig :: C.TypeSig -> CCheck TypeSig
checkTypeSig (C.Sig x e) ret = do
  (n, a) <- checkScheme e
  bindName (mkDefInfo x n) $ \x -> ret (Sig x a)

checkFields :: [NameInfo] -> [C.Constr] -> CCheck [TypeSig]
checkFields ps fs ret = mapC bindName ps $ \_ -> do
  fs <- mapC (checkField ps) fs return
  mapC bindField fs ret
  where
    bindField :: (C.Name, Int, Expr) -> CCheck TypeSig
    bindField (x, n, a) ret = bindName (mkProjInfo x n) $ \x -> ret (Sig x a)

checkField :: [NameInfo] -> C.Constr -> CCheck (C.Name, Int, Expr)
checkField xs (C.Constr c e) ret =
  mapC bindName xs $ \_ -> do
    (n, a) <- checkScheme e
    bindName (mkVarInfo c) $ \_ -> ret (c, n, a)

getFields :: C.Fields -> [C.Constr]
getFields C.NoFields    = []
getFields (C.Fields fs) = fs

checkConstructor :: Expr -> [NameInfo] -> C.Constr -> CCheck TypeSig
checkConstructor d xs (C.Constr c e) ret =
  mapC bindName xs $ \_ -> do
    (n, a) <- checkScheme e
    args   <- checkConstructorType a d (map infoName xs)
    bindName (mkConInfo c n args) $ \c -> ret (Sig c a)

checkScheme :: C.Expr -> Check (Hiding, Expr)
checkScheme e = do
  let (n, e') = countFirstHidden e
  a <- checkExpr e'
  return (n, a)

checkConstructorType :: Expr
                        -- ^ The constructor's type.
                     -> Expr
                        -- ^ The data type applied to its parameters.
                     -> [Name]
                        -- ^ The parameters.
                     -> Check NumberOfArguments
                        -- ^ The number of constructor arguments is
                        -- returned.
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
cMeta x = C.App [C.Arg $ C.Id $ C.Name ((l, c), "_")]
  where SrcLoc l c = srcLoc x

cWild :: HasSrcLoc a => a -> C.Pattern
cWild x = C.IdP (C.Name ((l, c), "_"))
  where SrcLoc l c = srcLoc x

insertImplicit :: SrcLoc -> Hiding -> [C.Arg] -> Check [C.Expr]
insertImplicit p 0 (C.Arg e : args)  = (e :) <$> insertImplicit (srcLoc e) 0 args
insertImplicit p 0 (C.HArg e : _)    = scopeError e $ "Unexpected implicit application " ++ C.printTree e
insertImplicit p 0 []                = return []
insertImplicit p n (C.HArg e : args) = (e :) <$> insertImplicit (srcLoc e) (n - 1) args
insertImplicit p n args              = (cMeta p :) <$> insertImplicit p (n - 1) args

insertImplicitPatterns :: SrcLoc -> Hiding -> [C.Pattern] -> Check [C.Pattern]
insertImplicitPatterns p 0 (C.HideP e : _)  = scopeError e $ "Unexpected implicit pattern " ++ C.printTree e
insertImplicitPatterns p 0 (e : args)       = (e :) <$> insertImplicitPatterns (srcLoc e) 0 args
insertImplicitPatterns p 0 []               = return []
insertImplicitPatterns p n (C.HideP e : ps) = (e :) <$> insertImplicitPatterns (srcLoc e) (n - 1) ps
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
      mi <- resolveName'' x
      case mi of
        Just ConName{} -> checkCon x [] ret
        _              -> bindName (mkVarInfo x) $ ret . VarP
    (c, ps) -> checkCon c ps ret
  where
    checkCon c ps ret = do
      (name, hiding, numargs) <- resolveCon c
      ps <- insertImplicitPatterns (srcLoc c) hiding ps
      checkNumberOfConstructorArguments p name numargs ps
      mapC checkPattern ps $ \ps -> ret (ConP name ps)

checkExpr :: C.Expr -> Check Expr
checkExpr e = case e of
  C.Pi (C.Tel tel) b ->
    checkTel tel $ \tel -> do
      b <- checkExpr b
      return $ foldr (uncurry Pi) b tel
  C.Fun a b -> Fun <$> checkExpr a <*> checkExpr b
  C.Lam xs e ->
    mapC (bindName . mkVarInfo) xs $ \xs ->
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
                doProj x e . map eapply =<< checkArgs e n es
            IsRefl p     -> Refl p <$ noArguments "refl"          p es
            HeadSet p    -> Set  p <$ noArguments "Set"           p es
            HeadMeta p   -> Meta p <$ noArguments "meta variable" p es
            IsCon c args -> Con c <$> do
              checkNumberOfConstructorArguments e c args =<< checkArgs z n es
            Other h      -> App h . map eapply <$> checkArgs z n es
    doProj x (App h es1) es2 = return $ App h (es1 ++ [Proj x] ++ es2)
    doProj x e _ = scopeError x $ "Cannot project " ++ show x ++ " from " ++ show e
    noArguments x p [] = return ()
    noArguments x p es = scopeError p $ "unexpected arguments to " ++ x ++ ": " ++ show es

checkArgs :: HasSrcLoc a =>
             a -> Hiding -> [C.Arg] ->
             Check [Expr]
checkArgs x n es = mapM checkExpr =<< insertImplicit (srcLoc x) n es

checkNumberOfConstructorArguments ::
  HasSrcLoc e => e -> Name -> NumberOfArguments -> [a] -> Check [a]
checkNumberOfConstructorArguments loc c args as = do
  when (nas < args) $
    scopeError loc $ "The constructor " ++ show c ++
                     " is applied to too few arguments."
  when (nas > args) $
    scopeError loc $ "The constructor " ++ show c ++
                     " is applied to too many arguments."
  return as
  where nas = length as


-- | The possible shapes of heads of an application
data AppHead
  = IsProj Name                   -- ^ Prefix projection.
  | IsCon Name NumberOfArguments  -- ^ Constructor.
  | IsRefl SrcLoc                 -- ^ @refl@.
  | HeadSet SrcLoc                -- ^ @Set@.
  | HeadMeta SrcLoc               -- ^ @_@.
  | Other Head                    -- ^ Variable, function, data, record, @J@.

instance HasSrcLoc AppHead where
  srcLoc h = case h of
    IsProj x     -> srcLoc x
    IsCon c _    -> srcLoc c
    IsRefl p     -> p
    Other h      -> srcLoc h
    HeadSet p    -> p
    HeadMeta p   -> p

data AppView = CApp C.Name [C.Arg]
             | NotApp C.Expr

appView :: C.Expr -> Check AppView
appView e = case e of
-- TODO: Maybe allow implicit arguments to be given for function applications?
  C.App (arg@C.HArg{} : _) ->
    scopeError arg $ "Unexpected curly braces: " ++ C.printTree arg
  C.App (C.Arg e : es) -> applyTo es =<< appView e
  C.App []             -> impossible "appView: empty application"
  C.Id x               -> return $ CApp x []
  C.Lam n e            -> notApp
  C.Pi{}               -> notApp
  C.Fun{}              -> notApp
  C.Eq{}               -> notApp
  where
    notApp = return $ NotApp e
    applyTo []  app          = return app
    applyTo es2 (CApp x es1) = return $ CApp x $ es1 ++ es2
    applyTo es  (NotApp e)   = scopeError e $ C.printTree e ++ " cannot be applied to arguments"

checkAppHead :: C.Name -> Check (AppHead, Hiding)
checkAppHead (C.Name ((l, c), "_"))    = return (HeadMeta  $ SrcLoc l c, 0)
checkAppHead (C.Name ((l, c), "Set"))  = return (HeadSet   $ SrcLoc l c, 0)
checkAppHead (C.Name ((l, c), "J"))    = return (Other $ J $ SrcLoc l c, 3)
checkAppHead (C.Name ((l, c), "refl")) = return (IsRefl    $ SrcLoc l c, 0)
checkAppHead x = do
  i <- resolveName' x
  case i of
    ProjName x n  -> return (IsProj x, n)
    VarName x     -> return (Other $ Var x, 0)
    ConName x n a -> return (IsCon x a, n)
    DefName x n   -> return (Other $ Def x, n)

checkTel :: [C.Binding] -> CCheck [(Name, Expr)]
checkTel = concatMapC checkBinding

checkBinding :: C.Binding -> CCheck [(Name, Expr)]
checkBinding b@C.HBind{} _ = scopeError b $ "Implicit binding must be on top level: " ++ C.printTree b
checkBinding (C.Bind args e) ret = do
  xs <- mapM argName args
  let is = map mkVarInfo xs
  a <- checkExpr e
  mapC bindName is $ \ys -> ret [ (y, a) | y <- ys ]

argName :: C.Arg -> Check C.Name
argName (C.Arg (C.Id x)) = return x
argName a = scopeError a $ "Expected variable name: " ++ C.printTree a

-- SrcLoc instances --

instance HasSrcLoc C.Name where
  srcLoc (C.Name ((l, c), _)) = SrcLoc l c

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
    C.Postulate (d:_) -> srcLoc d
    C.Postulate []     -> noSrcLoc
    C.TypeSig x        -> srcLoc x
    C.Data x _ _       -> srcLoc x
    C.Record x _ _     -> srcLoc x
    C.FunDef x _ _ _   -> srcLoc x
    C.Open x           -> srcLoc x
    C.Import x         -> srcLoc x

instance HasSrcLoc C.Pattern where
  srcLoc p = case p of
    C.IdP x    -> srcLoc x
    C.AppP p _ -> srcLoc p
    C.HideP p  -> srcLoc p

