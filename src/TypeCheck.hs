{-# LANGUAGE OverloadedStrings #-}
module TypeCheck (checkProgram, TCState') where

import           Prelude                          hiding (abs, pi)

import           Data.Functor                     ((<$>), (<$))
import           Data.Foldable                    (forM_, toList, Foldable)
import qualified Data.HashSet                     as HS
import           Control.Monad                    (when, void, guard, mzero, forM, msum, join)
import           Data.List                        (sortBy, groupBy)
import           Data.Traversable                 (traverse, sequenceA, Traversable)
import           Prelude.Extras                   ((==#))
import           Bound                            (Var(F, B), Bound, (>>>=), Scope(Scope), fromScope)
import           Bound.Var                        (unvar)
import           Data.Typeable                    (Typeable)
import           Data.Void                        (vacuous, Void, vacuousM, absurd)
import qualified Data.Set                         as Set
import qualified Data.Map                         as Map
import           Control.Applicative              (Applicative(pure, (<*>)))
import           Control.Monad.Trans              (lift)
import           Control.Monad.Trans.Either       (EitherT(EitherT), runEitherT)
import           Control.Monad.Trans.Maybe        (MaybeT(MaybeT), runMaybeT)
import           Data.Function                    (on)
import           Data.Ord                         (comparing)

import qualified Text.PrettyPrint.Extended        as PP
import           Text.PrettyPrint.Extended        (($$), (<>), (<+>), render)
import           Syntax.Internal                  (Name)
import qualified Syntax.Internal                  as A
import           Term
import qualified Term.Context                     as Ctx
import qualified Term.Telescope                   as Tel
import qualified Term.Signature                   as Sig
import           TypeCheck.Monad

-- Useful types
------------------------------------------------------------------------

type Ctx t v = Ctx.ClosedCtx t v

type TC'      t a = TC      t (TypeCheckProblem t) a
type StuckTC' t a = StuckTC t (TypeCheckProblem t) a

type TCState' t = TCState t (TypeCheckProblem t)

-- Type checking
------------------------------------------------------------------------

-- Checking programs
--------------------

checkProgram
    :: ∀ t. (IsTerm t) => [A.Decl] -> IO (Either PP.Doc (TCState' t))
checkProgram decls0 = do
    drawLine
    putStrLn "-- Checking declarations"
    drawLine
    runEitherT (goDecls initTCState decls0)
  where
    goDecls :: TCState' t -> [A.Decl] -> EitherT PP.Doc IO (TCState' t)
    goDecls ts [] = do
      lift $ report ts
      return ts
    goDecls ts (decl : decls) = do
      lift $ putStrLn $ render decl
      ((), ts') <- EitherT $ runTC typeCheckProblem ts $ checkDecl decl >> solveProblems_
      goDecls ts' decls

    report :: TCState' t -> IO ()
    report ts = do
      let tr  = tcReport ts
      let mvsTypes  = Sig.metaVarsTypes $ trSignature tr
      let mvsBodies = Sig.metaVarsBodies $ trSignature tr
      drawLine
      putStrLn $ "-- Solved MetaVars: " ++ show (Map.size mvsBodies)
      putStrLn $ "-- Unsolved MetaVars: " ++ show (Map.size mvsTypes - Map.size mvsBodies)
      drawLine
      forM_ (Map.toList mvsTypes) $ \(mv, mvType) -> do
        putStrLn $ render $
          PP.pretty mv <+> ":" <+> PP.nest 2 (PP.pretty (view mvType))
        let mvBody = case Map.lookup mv mvsBodies of
              Nothing      -> "?"
              Just mvBody0 -> prettyView mvBody0
        putStrLn $ render $ PP.pretty mv <+> "=" <+> PP.nest 2 mvBody
        putStrLn ""
      drawLine
      putStrLn $ "-- Solved problems: " ++ show (Set.size (trSolvedProblems tr))
      putStrLn $ "-- Unsolved problems: " ++ show (Map.size (trUnsolvedProblems tr))
      drawLine
      -- forM_ (Map.toList (trUnsolvedProblems tr)) $ \(pid, (probState, probDesc)) -> do
      --   let desc = render $
      --         PP.pretty pid $$
      --         PP.nest 2 (PP.pretty probState) $$
      --         PP.nest 2 probDesc
      --   putStrLn desc
      --   putStrLn ""

    drawLine =
      putStrLn "------------------------------------------------------------------------"

checkDecl :: (IsTerm t) => A.Decl -> TC' t ()
checkDecl decl = atSrcLoc decl $ do
  case decl of
    A.TypeSig sig      -> checkTypeSig sig
    A.DataDef d xs cs  -> checkData d xs cs
    A.RecDef d xs c fs -> checkRec d xs c fs
    A.FunDef f clauses -> checkFunDef f clauses

checkTypeSig :: (IsTerm t) => A.TypeSig -> TC' t ()
checkTypeSig (A.Sig name absType) = do
    type_ <- isType Ctx.Empty absType
    addConstant name Postulate type_

checkData
    :: (IsTerm t)
    => Name
    -- ^ Name of the tycon.
    -> [Name]
    -- ^ Names of parameters to the tycon.
    -> [A.TypeSig]
    -- ^ Types for the data constructors.
    -> TC' t ()
checkData tyCon tyConPars dataCons = do
    tyConType <- definitionType <$> getDefinition tyCon
    addConstant tyCon (Data []) tyConType
    unrollPiWithNamesTC tyConType tyConPars $ \tyConPars' endType -> do
        elimStuckTC (equalType tyConPars' endType set) $
          error $ "Type constructor does not return Set: " ++ show tyCon
        let appliedTyConType = ctxApp (def tyCon []) tyConPars'
        mapM_ (checkConstr tyCon tyConPars' appliedTyConType) dataCons

checkConstr
    :: (IsVar v, IsTerm t)
    => Name
    -- ^ Name of the tycon.
    -> Ctx.ClosedCtx (Type t) v
    -- ^ Ctx with the parameters of the tycon.
    -> Type t v
    -- ^ Tycon applied to the parameters.
    -> A.TypeSig
    -- ^ Data constructor.
    -> TC' t ()
checkConstr tyCon tyConPars appliedTyConType (A.Sig dataCon synDataConType) = do
    atSrcLoc dataCon $ do
        dataConType <- isType tyConPars synDataConType
        unrollPiTC dataConType $ \vs endType -> do
            let appliedTyConType' = fmap (Ctx.weaken vs) appliedTyConType
            elimStuckTC (equalType (tyConPars Ctx.++ vs) appliedTyConType' endType) $ do
              checkError $ TermsNotEqual appliedTyConType' endType
        addDataCon dataCon tyCon (Tel.idTel tyConPars dataConType)

checkRec
    :: (IsTerm t)
    => Name
    -- ^ Name of the tycon.
    -> [Name]
    -- ^ Name of the parameters to the tycon.
    -> Name
    -- ^ Name of the data constructor.
    -> [A.TypeSig]
    -- ^ Fields of the record.
    -> TC' t ()
checkRec tyCon tyConPars dataCon fields = do
    tyConType <- definitionType <$> getDefinition tyCon
    addConstant tyCon (Record dataCon []) tyConType
    unrollPiWithNamesTC tyConType tyConPars $ \tyConPars' endType -> do
        void $ equalType tyConPars' endType set
        fieldsTel <- checkFields tyConPars' fields
        let appliedTyConType = ctxApp (def tyCon []) tyConPars'
        addProjections
          tyCon tyConPars' (boundTermVar "_") (map A.typeSigName fields)
          (fmap F fieldsTel)
        Tel.unTel fieldsTel $ \fieldsCtx Tel.Proxy ->
            addDataCon dataCon tyCon $
            Tel.idTel tyConPars' $
            ctxPi fieldsCtx (fmap (Ctx.weaken fieldsCtx) appliedTyConType)

checkFields
    :: forall v t. (IsVar v, IsTerm t)
    => Ctx t v -> [A.TypeSig] -> TC' t (Tel.ProxyTel (Type t) v)
checkFields ctx0 = go Ctx.Empty
  where
    go :: forall v' . (IsVar v')
       => Ctx.Ctx v (Type t) v' -> [A.TypeSig] -> TC' t (Tel.ProxyTel (Type t) v)
    go ctx [] =
        return $ Tel.proxyTel ctx
    go ctx (A.Sig field synFieldType : fields) = do
        fieldType <- isType (ctx0 Ctx.++ ctx) synFieldType
        go (Ctx.Snoc ctx (field, fieldType)) fields

addProjections
    :: (IsVar v, IsTerm t)
    => Name
    -- ^ Type constructor.
    -> Ctx (Type t) v
    -- ^ A context with the parameters to the type constructor.
    -> TermVar v
    -- ^ Variable referring to the value of type record type itself,
    -- which is the last argument of each projection ("self").  We have
    -- a 'TermVar' here (and after) precisely because we're scoping over
    -- the self element after the tycon parameters above.
    -> [Name]
    -- ^ Names of the remaining fields.
    -> Tel.ProxyTel (Type t) (TermVar v)
    -- ^ Telescope holding the types of the next fields, scoped
    -- over the types of the previous fields.
    -> TC' t ()
addProjections tyCon tyConPars self fields0 =
    go $ zip fields0 $ map Field [0,1..]
  where
    go fields fieldTypes = case (fields, fieldTypes) of
      ([], Tel.Empty Tel.Proxy) ->
        return ()
      ((field, ix) : fields', Tel.Cons (_, fieldType) fieldTypes') -> do
        let endType = pi (ctxApp (def tyCon []) tyConPars) (toAbs fieldType)
        addProjection field ix tyCon (Tel.idTel tyConPars endType)
        go fields' $
         Tel.instantiate fieldTypes' $ unview $ App (Var self) [Proj field ix]
      (_, _) -> error "impossible.addProjections: impossible: lengths do not match"

-- addProjections
--     :: forall v t.
--        (IsVar v, IsTerm t)
--     => Name
--     -- ^ Type constructor.
--     -> Ctx t v
--     -- ^ A context with the parameters to the type constructor, except
--     -- the last one ("self").
--     -> (Name, Type t v)
--     -- ^ Name and type for the the value of type record type itself,
--     -- which is the last argument of each projection ("self").  We have
--     -- a 'TermVar' in the context precisely because we're scoping over
--     -- the self element after the tycon parameters above.
--     -> [Name]
--     -- ^ Names of the remaining fields.
--     -> Tel.ProxyTel (Type t) (TermVar v)
--     -- ^ Telescope holding the types of the next fields, scoped
--     -- over the types of the previous fields.
--     -> TC' t ()
-- addProjections tyCon tyConPars (selfName, selfType) fields0 =
--     go $ zip fields0 $ map Field [0,1..]
--   where
--     tyConParsWithSelf = Ctx.Snoc tyConPars (selfName, selfType)
--     selfVar = boundTermVar selfName

--     go :: [(Name, Field)] -> Tel.ProxyTel (Type t) (TermVar v) -> TC' t ()
--     go fields fieldTypes = case (fields, fieldTypes) of
--       ([], Tel.Empty Tel.Proxy) ->
--         return ()
--       ((field, ix) : fields', Tel.Cons (_, fieldType) fieldTypes') -> do
--         let endType = pi (ctxApp (def tyCon []) tyConParsWithSelf) (toAbs fieldType)
--         addProjection field ix tyCon (Tel.idTel tyConParsWithSelf endType)
--         go fields' $
--           Tel.instantiate fieldTypes' $ unview $ App (Var selfVar) [Proj field ix]
--       (_, _) -> error "impossible.addProjections: impossible: lengths do not match"

-- TODO what about pattern coverage?

checkFunDef :: (IsTerm t) => Name -> [A.Clause] -> TC' t ()
checkFunDef fun synClauses = do
    funType <- definitionType <$> getDefinition fun
    clauses <- forM synClauses $ \(A.Clause synPats synClauseBody) -> do
      checkPatterns fun synPats funType $ \ctx pats _ clauseType -> do
        clauseBody <- check ctx synClauseBody clauseType
        return $ Clause pats $ Scope $ fmap (toIntVar ctx) clauseBody
    inv <- withSignature $ \sig -> checkInvertibility sig clauses
    addClauses fun inv
  where
    toIntVar ctx v = B $ Ctx.elemIndex v ctx

checkPatterns
    :: (IsVar v, IsTerm t, Typeable a)
    => Name
    -> [A.Pattern]
    -> Type t v
    -- ^ Type of the clause that has the given 'A.Pattern's in front.
    -> (∀ v'. (IsVar v') => Ctx.Ctx v (Type t) v' -> [Pattern] -> [Term t v'] -> Type t v' -> TC' t a)
    -- ^ Handler taking a context into the internal variable, list of
    -- internal patterns, a list of terms produced by them, and the type
    -- of the clause body (scoped over the pattern variables).
    -> TC' t a
checkPatterns _ [] type_ ret =
    ret Ctx.Empty [] [] type_
checkPatterns funName (synPat : synPats) type0 ret = atSrcLoc synPat $ do
  stuck <- matchPi_ type0 $ \dom cod -> fmap NotStuck $ do
    checkPattern funName synPat dom $ \ctx pat patVar -> do
      let cod'  = fmap (Ctx.weaken ctx) cod
      let cod'' = instantiate cod' patVar
      checkPatterns funName synPats cod'' $ \ctx' pats patsVars -> do
        let patVar' = fmap (Ctx.weaken ctx') patVar
        ret (ctx Ctx.++ ctx') (pat : pats) (patVar' : patsVars)
  checkPatternStuck funName stuck

checkPattern
    :: (IsVar v, IsTerm t, Typeable a)
    => Name
    -> A.Pattern
    -> Type t v
    -- ^ Type of the matched thing.
    -> (∀ v'. (IsVar v') => Ctx.Ctx v (Type t) v' -> Pattern -> Term t v' -> TC' t a)
    -- ^ Handler taking the context, the internal 'Pattern', and a
    -- 'Term' containing the term produced by it.
    -> TC' t a
checkPattern funName synPat type_ ret = case synPat of
    A.VarP name -> do
      ret (Ctx.singleton name type_) VarP (var (boundTermVar name))
    A.WildP _ -> do
      ret (Ctx.singleton "_" type_) VarP (var (boundTermVar "_"))
    A.ConP dataCon synPats -> do
      DataCon typeCon dataConType <- getDefinition dataCon
      typeConDef <- getDefinition typeCon
      case typeConDef of
        Constant (Data _)     _ -> return ()
        Constant (Record _ _) _ -> checkError $ PatternMatchOnRecord synPat typeCon
        _                       -> error $ "impossible.checkPattern" ++ render typeConDef
      stuck <- matchTyCon typeCon type_ $ \typeConArgs -> fmap NotStuck $ do
        let dataConTypeNoPars = Tel.substs (vacuous dataConType) typeConArgs
        checkPatterns funName synPats dataConTypeNoPars $ \ctx pats patsVars _ -> do
          let t = unview (Con dataCon patsVars)
          ret ctx (ConP dataCon pats) t
      checkPatternStuck funName stuck

-- TODO we can loosen this by postponing adding clauses.
checkPatternStuck :: (IsTerm t) => Name -> Stuck a -> TC' t a
checkPatternStuck funName stuck =
  case stuck of
    NotStuck x -> return x
    StuckOn _  -> checkError $ StuckTypeSignature funName

-- Checking
-----------

check
  :: (IsVar v, IsTerm t)
  => Ctx t v -> A.Expr -> Type t v -> TC' t (Term t v)
check ctx synT type_ = atSrcLoc synT $ case synT of
  A.Con dataCon synArgs -> do
    DataCon tyCon dataConType <- getDefinition dataCon
    metaVarIfStuck ctx type_ $ matchTyCon tyCon type_ $ \tyConArgs -> do
      let appliedDataConType = Tel.substs (vacuous dataConType) tyConArgs
      checkConArgs ctx synArgs appliedDataConType `bindStuckTC`
        WaitingOn (con dataCon)
  A.Refl _ -> do
    metaVarIfStuck ctx type_ $ matchEqual type_ $ \type' t1 t2 -> do
      checkEqual ctx type' t1 t2 `bindStuckTC` WaitingOn (\() -> refl)
  A.Meta _ ->
    addMetaVarInCtx ctx type_
  A.Lam name synBody -> do
    metaVarIfStuck ctx type_ $ matchPi name type_ $ \dom cod -> do
      body <- check (Ctx.Snoc ctx (name, dom)) synBody (fromAbs cod)
      returnStuckTC $ lam (toAbs body)
  _ -> do
    metaVarIfStuck ctx type_ $
      infer ctx synT `bindStuckTC` CheckEqualInfer ctx type_

    -- -- TODO Use combinators below, remove duplication with
    -- -- `metaVarIfStuck'.
    -- case stuck of
    --   NotStuck (t, type') -> do
    --     stuck' <- equalType type_ type'
    --     case stuck' of
    --       NotStuck () -> do
    --         return t
    --       StuckOn pid -> do
    --         mv <- addMetaVarInCtx type_
    --         void $ bindProblemCheckEqual pid type' mv t
    --         return mv
    --   StuckOn pid -> do
    --     mv <- addMetaVarInCtx type_
    --     void $ bindProblem pid (WaitForInfer synT type_) $ \(t, type') -> do
    --       stuck' <- equalType type_ type'
    --       case stuck' of
    --         NotStuck () ->
    --           checkEqual type_ mv t
    --         StuckOn pid' ->
    --           StuckOn <$> bindProblemCheckEqual pid' type_ mv t
    --     return mv


checkSpine
  :: (IsVar v, IsTerm t)
  => Ctx t v -> Term t v -> [A.Elim] -> Type t v -> StuckTC' t (Term t v, Type t v)
checkSpine _ h [] type_ =
  returnStuckTC (h, type_)
checkSpine ctx h (el : els) type_ = atSrcLoc el $ case el of
  A.Proj proj -> do
    applyProjection proj h type_ `bindStuckTC` CheckSpine ctx els
  A.Apply synArg -> do
    matchPi_ type_ $ \dom cod -> do
      arg <- check ctx synArg dom
      let cod' = instantiate cod arg
      let h' = eliminate h [Apply arg]
      checkSpine ctx h' els cod'

checkConArgs
  :: (IsVar v, IsTerm t)
  => Ctx t v -> [A.Expr] -> Type t v -> StuckTC' t [t v]
checkConArgs _ [] _ = do
  returnStuckTC []
checkConArgs ctx (synArg : synArgs) type_ = atSrcLoc synArg $ do
  matchPi_ type_ $ \dom cod -> do
    arg <- check ctx synArg dom
    checkConArgs ctx synArgs (instantiate cod arg) `bindStuckTC` WaitingOn (arg :)

isType :: (IsVar v, IsTerm t) => Ctx t v -> A.Expr -> TC' t (Type t v)
isType ctx abs = check ctx abs set

-- Inference
------------

infer
  :: (IsVar v, IsTerm t)
  => Ctx t v -> A.Expr -> StuckTC' t (Term t v, Type t v)
infer ctx synT = atSrcLoc synT $ case synT of
  A.Set _ ->
    returnStuckTC (set, set)
  A.Pi name synDomain synCodomain -> do
    domain   <- isType ctx synDomain
    codomain <- isType (Ctx.Snoc ctx (name, domain)) synCodomain
    returnStuckTC (pi domain (toAbs codomain), set)
  A.Fun synDomain synCodomain -> do
    infer ctx $ A.Pi "_" synDomain synCodomain
  A.App synH elims -> do
    (h, type_) <- inferHead ctx synH
    checkSpine ctx (app h []) elims type_
  A.Equal synType synX synY -> do
    type_ <- isType ctx synType
    x <- check ctx synX type_
    y <- check ctx synY type_
    returnStuckTC (equal type_ x y, set)
  _ -> do
    type_ <- addMetaVarInCtx ctx set
    t <- check ctx synT type_
    returnStuckTC (t, type_)

inferHead
  :: (IsVar v, IsTerm t)
  => Ctx t v -> A.Head -> TC' t (Head v, Type t v)
inferHead ctx synH = atSrcLoc synH $ case synH of
  A.Var name -> do
    case Ctx.lookupName name ctx of
      Nothing         -> checkError $ NameNotInScope name
      Just (v, type_) -> return (Var v, type_)
  A.Def name -> do
    type_ <- definitionType <$> getDefinition name
    return (Def name, vacuous type_)
  A.J{} ->
    return (J, vacuous $ typeOfJ)

-- (A : Set) ->
-- (x : A) ->
-- (y : A) ->
-- (P : (x : A) -> (y : A) -> (eq : _==_ A x y) -> Set) ->
-- (p : (x : A) -> P x x refl) ->
-- (eq : _==_ A x y) ->
-- P x y eq
typeOfJ :: forall t. (IsTerm t) => Closed (Type t)
typeOfJ = fmap close $
    ("A", set) -->
    ("x", var "A") -->
    ("y", var "A") -->
    ("P", ("x", var "A") --> ("y", var "A") -->
          ("eq", equal (var "A") (var "x") (var "y")) -->
          set
    ) -->
    ("p", ("x", var "A") --> app (Var "P") (map Apply [var "x", var "x", refl])) -->
    ("eq", equal (var "A") (var "x") (var "y")) -->
    app (Var "P") (map Apply [var "x", var "y", refl])
  where
    close :: Name -> Void
    close v = error $ "impossible.typeOfJ: Free variable " ++ PP.render v

    infixr 9 -->
    (-->) :: (Name, t Name) -> t Name -> t Name
    (x, type_) --> t = pi type_ $ abstract x t

-- Equality
------------

checkEqual
  :: (IsVar v, IsTerm t)
  => Ctx t v -> Type t v -> Term t v -> Term t v -> StuckTC' t ()
checkEqual ctx type_ x y = do
  typeView <- whnfViewTC type_
  expand <- withSignature $ \sig -> etaExpand sig typeView
  blockedX <- whnfTC $ expand x
  blockedY <- whnfTC $ expand y
  case (blockedX, blockedY) of
    (_, _) | blockedX ==# blockedY ->
      returnStuckTC ()
    (MetaVarHead mv elims, t) ->
      metaAssign ctx type_ mv elims (ignoreBlocking t)
    (t, MetaVarHead mv elims) ->
      metaAssign ctx type_ mv elims (ignoreBlocking t)
    (BlockedOn mvs1 _ _, BlockedOn mvs2 _ _) -> do
      -- Both blocked, and we already checked for syntactic equality: we
      -- give up.
      newProblem (Set.union mvs1 mvs2) $
        CheckEqual ctx (unview typeView) (ignoreBlocking blockedX) (ignoreBlocking blockedY)
    (BlockedOn mvs f elims, t) -> do
      checkEqualBlockedOn ctx (unview typeView) mvs f elims (ignoreBlocking t)
    (t, BlockedOn mvs f elims) -> do
      checkEqualBlockedOn ctx (unview typeView) mvs f elims (ignoreBlocking t)
    (NotBlocked x', NotBlocked y') -> case (typeView, view x', view y') of
      -- Note that here we rely on canonical terms to have canonical
      -- types, and on the terms to be eta-expanded.
      (Pi dom cod, Lam body1, Lam body2) -> do
        -- TODO there is a bit of duplication between here and expansion.
        let body1' = fromAbs body1
        let body2' = fromAbs body2
        let cod'   = fromAbs cod
        checkEqual (Ctx.Snoc ctx (getName_ body1', dom)) cod' body1' body2'
      (Set, Pi dom1 cod1, Pi dom2 cod2) -> do
        let cod1' = fromAbs cod1
        checkEqual ctx set dom1 dom2 `bindStuckTC`
          CheckEqual (Ctx.Snoc ctx (getName_ cod1', dom1)) set cod1' (fromAbs cod2)
      (Set, Equal type1 x1 y1, Equal type2 x2 y2) -> do
        checkEqual ctx set type1 type2 `bindStuckTC`
          CheckEqual ctx type1 x1 x2   `bindStuckTC`
          CheckEqual ctx type1 y1 y2
      (_, Refl, Refl) -> do
        returnStuckTC ()
      (App (Def _) tyConPars0, Con dataCon dataConArgs1, Con dataCon' dataConArgs2)
          | Just tyConPars <- mapM isApply tyConPars0
          , dataCon == dataCon' -> do
            DataCon _ dataConType <- getDefinition dataCon
            let appliedDataConType = Tel.substs (vacuous dataConType) tyConPars
            equalConArgs ctx appliedDataConType dataCon dataConArgs1 dataConArgs2
      (Set, Set, Set) -> do
        returnStuckTC ()
      (_, App h1 elims1, App h2 elims2) | h1 == h2 -> do
        equalSpine ctx h1 elims1 elims2
      (_, _, _) -> do
        checkError $ TermsNotEqual x y
  where
    etaExpand sig typeView =
      case typeView of
        App (Def tyCon) _ | isRecordType sig tyCon ->
          let Constant (Record dataCon projs) _ = Sig.getDefinition sig tyCon
          in \t ->
               def dataCon $ map (\(n, ix) -> Apply (eliminate t [Proj n ix])) projs
        Pi _ codomain ->
          let name = getName_ $ fromAbs codomain
              v    = var $ boundTermVar name
          in \t -> case view t of
               Lam _ -> t
               _     -> lam $ toAbs $ eliminate (fromAbs (weaken t)) [Apply v]
        _ ->
          id

checkEqualSpine
  :: (IsVar v, IsTerm t)
  => Ctx t v
  -> Type t v
  -- ^ Type of the head.
  -> Term t v
  -- ^ Head.
  -> [Elim (Term t) v]
  -> [Elim (Term t) v]
  -> StuckTC' t ()
checkEqualSpine _ _ _ [] [] =
  returnStuckTC ()
checkEqualSpine ctx type_ h (elim1 : elims1) (elim2 : elims2) = do
  case (elim1, elim2) of
    (Apply arg1, Apply arg2) -> do
      typeView <- whnfViewTC type_
      case typeView of
        Pi domain codomain -> do
          -- If you're stuck on the domain, don't give up, and put a
          -- metavariable instead.
          arg1' <- metaVarIfStuck ctx domain $
            checkEqual ctx domain arg1 arg2 `bindStuckTC` WaitingOn (\() -> arg1)
          checkEqualSpine ctx
            (instantiate codomain arg1') (eliminate h [Apply arg1']) elims1 elims2
        _ ->
          error $ "impossible.checkEqualSpine: Expected function type " ++ render typeView
    (Proj proj projIx, Proj proj' projIx')
      | proj == proj' && projIx == projIx' ->
        applyProjection proj h type_ `bindStuckTC`
          CheckEqualSpine ctx elims1 elims2
    _ ->
      checkError $ SpineNotEqual type_ (elim1 : elims1) (elim1 : elims2)
checkEqualSpine _ type_ _ elims1 elims2 = do
  checkError $ SpineNotEqual type_ elims1 elims2

equalSpine
  :: (IsVar v, IsTerm t)
  => Ctx t v -> Head v -> [Elim t v] -> [Elim t v] -> StuckTC' t ()
equalSpine ctx h elims1 elims2 = do
  hType <- case h of
    Var v   -> return $ Ctx.getVar v ctx
    Def f   -> vacuous . definitionType <$> getDefinition f
    J       -> return $ vacuous typeOfJ
    Meta mv -> vacuous <$> getMetaVarType mv
  checkEqualSpine ctx hType (app h []) elims1 elims2

-- | INVARIANT: the two lists are the of the same length.
equalConArgs
  :: (IsVar v, IsTerm t)
  => Ctx t v
  -> Type t v
  -- ^ Type of the head.
  -> Name -> [Term t v] -> [Term t v] -> StuckTC' t ()
equalConArgs ctx type_ dataCon xs ys = do
  expandedCon <- unrollPiTC type_ $ \ctx' _ ->
                 return $ ctxLam ctx' $ con dataCon $ map var $ ctxVars ctx'
  checkEqualSpine ctx type_ expandedCon (map Apply xs) (map Apply ys)

checkEqualBlockedOn
  :: forall t v.
     (IsVar v, IsTerm t)
  => Ctx t v
  -> Type t v
  -> Set.Set MetaVar -> Name -> [Elim t v]
  -> Term t v
  -> StuckTC' t ()
checkEqualBlockedOn ctx type_ mvs fun1 elims1 t2 = do
  Function _ clauses <- getDefinition fun1
  case clauses of
    NotInvertible _ -> do
      fallback
    Invertible injClauses1 -> do
      t2View <- whnfViewTC t2
      case t2View of
        App (Def fun2) elims2 | fun1 == fun2 -> do
          equalSpine ctx (Def fun1) elims1 elims2
        _ -> do
          t2Head <- withSignature $ \sig -> termHead sig (unview t2View)
          case t2Head of
            Nothing -> do
              fallback
            Just tHead | Just (Clause pats _) <- lookup tHead injClauses1 -> do
              -- Make the eliminators match the patterns
              matchPats pats elims1
              -- And restart
              checkEqual ctx type_ t1 t2
            Just _ -> do
              checkError $ TermsNotEqual t1 t2
  where
    t1 = ignoreBlocking (BlockedOn mvs fun1 elims1)
    fallback = newProblem mvs $ CheckEqual ctx type_ t1 t2

    matchPats :: [Pattern] -> [Elim t v] -> TC' t ()
    matchPats [] [] = do
      return ()
    matchPats (VarP : pats) (_ : elims) = do
      matchPats pats elims
    matchPats (ConP dataCon pats' : pats) (elim : elims) = do
      matchPat dataCon pats' elim
      matchPats pats elims
    matchPats [] _ = do
      -- Less patterns than arguments is fine.
      return ()
    matchPats _ [] = do
      -- Less arguments than patterns is not fine -- we know that the
      -- eliminators were blocked on the patterns.
      error "impossible.checkEqualBlockedOn: got too few patterns."

    matchPat :: Name -> [Pattern] -> Elim t v -> TC' t ()
    matchPat dataCon pats (Apply t) = do
      tView <- whnfViewTC t
      case tView of
        App (Meta mv) mvArgs -> do
          mvT <- instantiateDataCon mv dataCon
          matchPat dataCon pats $ Apply $ eliminate (vacuous mvT) mvArgs
        Con dataCon' dataConArgs | dataCon == dataCon' ->
          matchPats pats (map Apply dataConArgs)
        _ ->
          -- This can't happen -- we know that the execution was
          -- blocked, or in other words it was impeded only by
          -- metavariables.
          error $ "impossible.matchPat: bad elim:\n" ++
                  show (ConP dataCon pats) ++ "\n" ++ render (Apply t)
    matchPat dataCon pats elim = do
      -- Same as above.
      error $ "impossible.matchPat: bad elim:\n" ++
              show (ConP dataCon pats) ++ "\n" ++ render elim

equalType :: (IsVar v, IsTerm t) => Ctx t v -> Type t v -> Type t v -> StuckTC' t ()
equalType ctx a b = checkEqual ctx set a b

-- Unification
------------------------------------------------------------------------

metaAssign
  :: (IsVar v, IsTerm t)
  => Ctx t v -> Type t v -> MetaVar -> [Elim (Term t) v] -> Term t v
  -> StuckTC' t ()
metaAssign ctx0 type0 mv elims0 t0 = do
  -- Try to eta-expand the metavariable first.
  mvType <- getMetaVarType mv
  -- If you can, eta-expand and restart the equality.  Otherwise, try to
  -- assign.
  mbRecordDataCon <- unrollPiTC mvType $ \_ mvEndType -> do
    withSignature $ \sig -> case whnfView sig mvEndType of
      App (Def tyCon) _ | Constant (Record dataCon _) _ <- Sig.getDefinition sig tyCon ->
        Just dataCon
      _ ->
        Nothing
  case mbRecordDataCon of
    Just dataCon -> do
      mvT <- instantiateDataCon mv dataCon
      checkEqual ctx0 type0 (eliminate (vacuous mvT) elims0) t0
    Nothing -> do
      etaExpandVarsTC ctx0 elims0 type0 t0 $ \ctx elims type_ t -> do
        -- See if we can invert the metavariable
        ttInv <- withSignature $ \sig -> invertMeta sig elims
        let invOrMvs = case ttInv of
              TTOK inv       -> Right inv
              TTMetaVars mvs -> Left $ Set.insert mv mvs
              -- TODO here we should also wait on metavars on the right that
              -- could simplify the problem.
              TTFail ()      -> Left $ Set.singleton mv
        case invOrMvs of
          Left mvs -> do
            t' <- withSignature $ \sig -> nf sig t
            -- TODO should we really prune allowing all variables here?  Or
            -- only the rigid ones?
            fvs <- withSignature $ \sig -> fvAll $ freeVars sig t'
            elims' <- withSignature $ \sig -> map (nf' sig) elims
            pruned <- prune fvs mv elims'
            if pruned
              then checkEqual ctx type_ (metaVar mv elims) t
              else newProblem mvs $ CheckEqual ctx type_ (metaVar mv elims) t
          Right inv -> do
            -- TODO have `pruneTerm' return an evaluated term.
            pruneTerm (Set.fromList $ toList inv) t
            t'0 <- withSignature $ \sig -> applyInvertMeta sig inv $ nf sig t
            case t'0 of
              TTOK t' -> do
                let mvs = metaVars t'
                when (mv `HS.member` mvs) $
                  checkError $ OccursCheckFailed mv t'
                instantiateMetaVar mv t'
                returnStuckTC ()
              TTMetaVars mvs ->
                newProblem (Set.insert mv mvs) $ CheckEqual ctx type_ (metaVar mv elims) t
              TTFail v ->
                checkError $ FreeVariableInEquatedTerm mv elims t v

-- | The term must be in normal form.
pruneTerm
    :: (IsVar v, IsTerm t)
    => Set.Set v                -- ^ allowed vars
    -> Term t v
    -> TC' t ()
pruneTerm vs t = do
  tView <- whnfViewTC t
  case tView of
    Lam body -> do
      let body' = fromAbs body
      pruneTerm (Set.insert (boundTermVar (getName_ body')) (Set.mapMonotonic F vs)) body'
    Pi domain codomain -> do
      pruneTerm vs domain
      let codomain' = fromAbs codomain
      pruneTerm (Set.insert (boundTermVar (getName_ codomain')) (Set.mapMonotonic F vs)) codomain'
    Equal type_ x y ->
      mapM_ (pruneTerm vs) [type_, x, y]
    App (Meta mv) elims ->
      void (prune vs mv elims) >> return ()
    App _ elims ->
      mapM_ (pruneTerm vs) [t' | Apply t' <- elims]
    Set ->
      return ()
    Refl ->
      return ()
    Con _ args ->
      mapM_ (pruneTerm vs) args

-- | Prunes a 'MetaVar' application and instantiates the new body.
-- Returns if some (not necessarely all) pruning was performed.
--
-- The term must be in normal form.
prune
    :: forall t v0.
       (IsVar v0, IsTerm t)
    => Set.Set v0               -- ^ allowed vars
    -> MetaVar
    -> [Elim (Term t) v0]       -- ^ Arguments to the metavariable
    -> TC' t Bool
prune allowedVs oldMv elims | Just args <- mapM isApply elims =
  maybe False (\() -> True) <$> runMaybeT (go args)
  where
    go args = do
      -- TODO check that newly created meta is well-typed.
      kills0 <- MaybeT $ withSignature $ \sig -> mapM (shouldKill sig allowedVs) args
      guard $ or kills0
      oldMvType <- lift $ getMetaVarType oldMv
      (newMvType, kills1) <- lift $ withSignature $ \sig -> createNewMeta sig oldMvType kills0
      guard $ any unNamed kills1
      newMv <- lift $ addMetaVar $ telPi newMvType
      lift $ instantiateMetaVar oldMv (createMetaLam newMv kills1)

    -- We build a telescope with only the non-killed types in.  This
    -- way, we can analyze the dependency between arguments and avoid
    -- killing things that later arguments depend on.
    --
    -- At the end of the telescope we put both the new metavariable and
    -- the remaining type, so that this dependency check will be
    -- performed on it as well.
    createNewMeta
      :: (IsVar v)
      => Sig.Signature t -> Type t v -> [Bool]
      -> (Tel.IdTel (Type t) v, [Named Bool])
    createNewMeta _ type_ [] =
      (Tel.Empty (Tel.Id type_), [])
    createNewMeta sig type_ (kill : kills) =
      case whnfView sig type_ of
        Pi domain codomain ->
          let codomain' = fromAbs codomain
              name = getName_ codomain'
              (tel, kills') = createNewMeta sig codomain' kills
              notKilled = (Tel.Cons (name, domain) tel, named name False : kills')
          in if not kill
             then notKilled
             else case traverse (unvar (const Nothing) Just) tel of
               Nothing   -> notKilled
               Just tel' -> (tel', named name True : kills')
        _ ->
          error "impossible.createPrunedMeta: metavar type too short"

    createMetaLam :: MetaVar -> [Named Bool] -> Closed (Type t)
    createMetaLam newMv = go' []
      where
        go' :: [v] -> [Named Bool] -> Type t v
        go' vs [] =
          metaVar newMv $ map (Apply . var) (reverse vs)
        go' vs (kill : kills) =
          let vs' = (if unNamed kill then [] else [B (() <$ kill)]) ++ map F vs
          in lam $ toAbs $ go' vs' kills
prune _ _ _ = do
  -- TODO we could probably do something more.
  return False

-- | Returns whether the term should be killed, given a set of allowed
-- variables.
shouldKill
  :: (IsTerm t, IsVar v)
  => Sig.Signature t -> Set.Set v -> Term t v -> Maybe Bool
shouldKill sig vs t = do
  case whnfView sig t of
    Lam _ ->
      mzero
    Con dataCon args | isRecordConstr sig dataCon ->
      and <$> mapM (shouldKill sig vs) args
    App (Def f) _ | not (isNeutral f) ->
      mzero
    Con _ _ ->
      mzero
    _ ->
      return $ not (fvRigid (freeVars sig t) `Set.isSubsetOf` vs)
  where
    -- | Check whether a term @Def f es@ could be reduced, if its arguments
    -- were different.
    isNeutral f =
      case Sig.getDefinition sig f of
        Constant{}    -> False
        DataCon{}     -> error $ "impossible.isNeutral: constructor " ++ show f
        Projection{}  -> error $ "impossible.isNeutral: projection " ++ show f
        Function{}    -> True
        -- TODO: more precise analysis
        -- We need to check whether a function is stuck on a variable
        -- (not meta variable), but the API does not help us...


data InvertMeta t v v0
  = IMSubst [(v0, t v)] [v]
  -- A substitution from variables of the term on the left of the
  -- equation to variables inside the metavar.
  --
  -- We also keep an ordered list of variables to abstract the body of
  -- the metavariable.
  | IMArgument (InvertMeta t (TermVar v) v0)
  deriving (Functor, Foldable, Traversable)

-- | Tries to invert a metavariable given its parameters (eliminators),
-- providing a substitution for the term on the right if it suceeds.
-- Doing so amounts to check if the pattern condition is respected for
-- the arguments, although we employ various trick to get around it when
-- the terms are not variables.
--
-- 'TTMetaVars' if the pattern condition check is blocked on a some
-- 'MetaVar's.  The set is empty if the pattern condition is not
-- respected and no 'MetaVar' can change that.
--
-- 'TTFail' if the pattern condition fails.
invertMeta
  :: forall v0 t.
     (IsVar v0, IsTerm t)
  => Sig.Signature t
  -> [Elim (Term t) v0]
  -> TermTraverse () (InvertMeta t v0 v0)
invertMeta sig elims0 = case mapM isApply elims0 of
    Just args0 -> go args0 [] (length args0)
    Nothing    -> TTFail ()     -- TODO eta-expand metavars to eliminate projections.
  where
    go :: [Term t v0] -> [v] -> Int -> TermTraverse () (InvertMeta t v v0)
    go args vs 0 =
      let vs' = reverse vs
      in case checkArgs (zip args (map var vs')) of
           TTFail ()      -> TTFail ()
           TTMetaVars mvs -> TTMetaVars mvs
           TTOK sub       -> IMSubst <$> checkLinearity sub <*> pure vs'
    go args vs n =
      IMArgument <$> go args (boundTermVar "_" : map F vs) (n - 1)

    checkArgs :: [(Term t v0, Term t v)] -> TermTraverse () [(v0, Term t v)]
    checkArgs xs = concat <$> traverse (uncurry checkArg) xs

    checkArg :: Term t v0 -> Term t v -> TermTraverse () [(v0, Term t v)]
    checkArg arg v = case whnf sig arg of
      NotBlocked t
        | App (Var v0) [] <- view t ->
          pure [(v0, v)]
      NotBlocked t
        | Con dataCon recArgs <- view t
        , DataCon tyCon _ <- Sig.getDefinition sig dataCon
        , Constant (Record _ fields) _ <- Sig.getDefinition sig tyCon ->
          checkArgs [ (recArg, eliminate v [Proj n f])
                    | (recArg, (n, f)) <- zip recArgs fields
                    ]
      NotBlocked _ ->
        TTFail ()
      MetaVarHead mv _ ->
        TTMetaVars $ Set.singleton mv
      BlockedOn mvs _ _ ->
        TTMetaVars mvs

    checkLinearity :: [(v0, Term t v)] -> TermTraverse () [(v0, Term t v)]
    checkLinearity sub =
      traverse makeLinear $ groupBy ((==) `on` fst) $ sortBy (comparing fst) sub

    makeLinear :: [(v0, Term t v)] -> TermTraverse () (v0, Term t v)
    makeLinear []      = error "impossible.checkPatternCondition"
    makeLinear [x]     = pure x
    -- TODO Consider making this work for singleton types.
    makeLinear (_ : _) = TTFail ()

applyInvertMeta
  :: forall t v0.
     (IsVar v0, IsTerm t)
  => Sig.Signature t -> InvertMeta t v0 v0 -> Term t v0
  -> TermTraverse v0 (Closed (Term t))
applyInvertMeta sig invMeta = go invMeta
  where
    go :: (IsVar v)
       => InvertMeta t v v0 -> Term t v0 -> TermTraverse v0 (Closed (Term t))
    go (IMSubst    sub vs) t = fmap kill . lambdaAbstract vs <$>
                               applyInvertMetaSubst sig sub t
    go (IMArgument im)     t = go im t

    kill = error "applyInvertMeta.impossible"

-- | Creates a term in the same context as the original term but lambda
-- abstracted over the given variables.
lambdaAbstract :: (IsVar v, IsTerm t) => [v] -> Term t v -> Term t v
lambdaAbstract []       t = t
lambdaAbstract (v : vs) t = unview $ Lam $ abstract v $ lambdaAbstract vs t

-- TODO improve efficiency of this traversal, we shouldn't need all
-- those `fromAbs'.  Also in `freeVars'.
applyInvertMetaSubst
    :: forall t v0 mvV.
       (IsVar v0, IsVar mvV, IsTerm t)
    => Sig.Signature t -> [(v0, t mvV)] -> Term t v0
    -> TermTraverse v0 (Term t mvV)
applyInvertMetaSubst sig subst t0 =
  flip go t0 $ \v -> maybe (Left v) Right (lookup v subst)
  where
    lift' :: forall v v1.
             (v -> Either v0 (Term t v1))
          -> (TermVar v -> Either v0 (Term t (TermVar v1)))
    lift' _ (B v) = Right $ var $ B v
    lift' f (F v) = fmap F <$> f v

    go :: forall v v1. (IsVar v, IsVar v1)
       => (v -> Either v0 (Term t v1)) -> Term t v -> TermTraverse v0 (t v1)
    go invert t =
      case whnfView sig t of
        Lam body ->
          (lam . toAbs) <$> go (lift' invert) (fromAbs body)
        Pi dom cod ->
          (\dom' cod' -> pi dom' (toAbs cod'))
            <$> go invert dom <*> go (lift' invert) (fromAbs cod)
        Equal type_ x y ->
          (\type' x' y' -> equal type' x' y')
            <$> (go invert type_) <*> (go invert x) <*> (go invert y)
        Refl ->
          pure refl
        Con dataCon args ->
          con dataCon <$> sequenceA (map (go invert) args)
        Set ->
          pure set
        App h elims ->
          let goElim (Apply t') = Apply <$> go invert t'
              goElim (Proj n f) = pure $ Proj n f

              resElims = traverse goElim elims
          in case (h, resElims) of
               (Meta mv, TTMetaVars mvs) ->
                 TTMetaVars $ Set.insert mv mvs
               (Meta mv, TTFail _) ->
                 TTMetaVars $ Set.singleton mv
               (Var v, _) ->
                 eliminate <$> either TTFail pure (invert v) <*> resElims
               (Def f, _) ->
                 app (Def f) <$> resElims
               (J, _) ->
                 app J <$> resElims
               (Meta mv, _) ->
                 app (Meta mv) <$> resElims

-- Eta-expansion of arguments of metas
--------------------------------------

data EtaExpandVars t f v = EtaExpandVars [Elim f v] (t f v)

instance (Bound t) => Bound (EtaExpandVars t) where
  EtaExpandVars elims t >>>= f = EtaExpandVars (map (>>>= f) elims) (t >>>= f)

etaExpandVarsTC
  :: (IsVar v, IsTerm t)
  => Ctx.ClosedCtx t v
  -> [Elim t v]
  -> Type t v
  -> Term t v
  -> (forall v'. (IsVar v') => Ctx.ClosedCtx t v' -> [Elim t v'] -> Type t v' -> Term t v' -> TC' t a)
  -> TC' t a
etaExpandVarsTC ctx elims type_ t ret = do
  join $ withSignature $ \sig ->
    etaExpandVars sig ctx elims (Tel.Prod2 type_ t) $ \ctx' elims' (Tel.Prod2 type' t') ->
      ret ctx' elims' type' t'

etaExpandVars
  :: (IsVar v, IsTerm f, Bound t)
  => Sig.Signature f
  -> Ctx.ClosedCtx f v
  -> [Elim f v]
  -> t f v
  -> (forall v'. (IsVar v') => Ctx.ClosedCtx f v' -> [Elim f v'] -> t f v' -> a)
  -> a
etaExpandVars sig ctx0 elims0 t ret =
  let elims = map (etaContractElim sig . nf' sig) elims0
  in case collectProjectedVar sig elims of
    Nothing ->
      ret ctx0 elims t
    Just (v, tyCon) ->
      splitContext ctx0 v (EtaExpandVars elims t) $ \ctx1 type_ tel ->
        let tel' = etaExpandVar sig tyCon type_ tel
        in Tel.unTel tel' $ \ctx2 (EtaExpandVars elims' t') ->
           etaExpandVars sig (ctx1 Ctx.++ ctx2) elims' t' ret

-- | Expands a record-typed variable ranging over the given 'Tel.Tel',
-- returning a new telescope ranging over all the fields of the record
-- type and the old telescope with the variable substituted with a
-- constructed record.
etaExpandVar
  :: (IsVar v, IsTerm f, Bound t)
  => Sig.Signature f
  -> Name
  -- ^ The type constructor of the record type.
  -> Type f v
  -- ^ The type of the variable we're expanding.
  -> Tel.Tel t f (TermVar v)
  -> Tel.Tel t f v
etaExpandVar sig tyCon type_ tel =
  let Constant (Record dataCon projs) _ = Sig.getDefinition sig tyCon
      DataCon _ dataConType = Sig.getDefinition sig dataCon
      App (Def _) tyConPars0 = whnfView sig type_
      Just tyConPars = mapM isApply tyConPars0
      appliedDataConType = Tel.substs (vacuous dataConType) tyConPars
      Right tel'' = unrollPiWithNames sig appliedDataConType (map fst projs) $ \dataConPars _ ->
        let tel' = tel >>>= \v -> case v of
                     B _  -> con dataCon $ map var $ ctxVars dataConPars
                     F v' -> var $ Ctx.weaken dataConPars v'
        in dataConPars Tel.++ tel'
  in tel''

-- | Scans a list of 'Elim's looking for an 'Elim' composed of projected
-- variable.
collectProjectedVar
  :: (IsVar v, IsTerm t) => Sig.Signature t -> [Elim t v] -> Maybe (v, Name)
collectProjectedVar sig elims = do
  (v, projName) <- msum $ flip map elims $ \elim -> do
    Apply t <- return elim
    App (Var v) vElims <- return $ whnfView sig t
    projName : _ <- forM vElims $ \vElim -> do
      Proj projName _ <- return vElim
      return projName
    return (v, projName)
  let Projection _ tyCon _ = Sig.getDefinition sig projName
  return (v, tyCon)

splitContext
  :: forall t f v0 a.
     Ctx.ClosedCtx f v0
  -> v0
  -> t f v0
  -> (forall v'. (IsVar v') => Ctx.ClosedCtx f v' -> Type f v' -> Tel.Tel t f (TermVar v') -> a)
  -> a
splitContext ctx0 v0 t ret = go ctx0 v0 (Tel.Empty t)
  where
    go :: Ctx.ClosedCtx f v -> v -> Tel.Tel t f v -> a
    go Ctx.Empty                 v     _   = absurd v
    go (Ctx.Snoc ctx (_, type_)) (B _) tel = ret ctx type_ tel
    go (Ctx.Snoc ctx type_)      (F v) tel = go ctx v (Tel.Cons type_ tel)

-- Eta-contraction of terms
---------------------------

etaContractElim :: (IsVar v, IsTerm t) => Sig.Signature t -> Elim t v -> Elim t v
etaContractElim sig (Apply t)  = Apply $ etaContract sig t
etaContractElim _   (Proj n f) = Proj n f

etaContract :: (IsVar v, IsTerm t) => Sig.Signature t -> t v -> t v
etaContract sig t0 = case whnfView sig t0 of
  -- TODO it should be possible to do it also for constructors
  Lam body
    | App h elims@(_:_) <- whnfView sig (etaContract sig (fromAbs body))
    , Apply t <- last elims
    , App (Var (B _)) [] <- whnfView sig t
    , Just t' <- traverse (unvar (const Nothing) Just) (app h (init elims)) ->
      t'
  Con dataCon args
    | DataCon tyCon _ <- Sig.getDefinition sig dataCon
    , Constant (Record _ fields) _ <- Sig.getDefinition sig tyCon
    , length args == length fields
    , Just (t : ts) <- sequence (zipWith isRightProjection fields args)
    , all (t ==#) ts ->
      t
  _ ->
    t0
  where
    isRightProjection (n, f) t
      | App h elims@(_ : _) <- whnfView sig (etaContract sig t)
      , Proj n' f' <- last elims
      , n == n', f == f' =
        Just $ nf sig $ app h (init elims)
    isRightProjection _ _ =
      Nothing

-- MetaVar handling
------------------------------------------------------------------------

addMetaVarInCtx
  :: (IsVar v, IsTerm t)
  => Ctx t v -> Type t v -> TC' t (Term t v)
addMetaVarInCtx ctx type_ = do
  mv <- addMetaVar $ ctxPi ctx type_
  return $ ctxApp (metaVar mv []) ctx

createMvsPars
  :: (IsVar v, IsTerm t) => Ctx t v -> Tel.IdTel (Type t) v -> TC' t [Term t v]
createMvsPars _ (Tel.Empty _) =
  return []
createMvsPars ctx (Tel.Cons (_, type') tel) = do
  mv  <- addMetaVarInCtx ctx type'
  mvs <- createMvsPars ctx (Tel.instantiate tel mv)
  return (mv : mvs)

-- Problem handling
------------------------------------------------------------------------

data TypeCheckProblem (t :: * -> *) a b where
  WaitingOn :: (a -> b) -> TypeCheckProblem t a b

  CheckEqual1     :: (IsVar v)
                  => Ctx t v -> Type t v -> Term t v
                  -> TypeCheckProblem t (Term t v) ()
  CheckEqualInfer :: (IsVar v)
                  => Ctx t v -> Type t v
                  -> TypeCheckProblem t (Term t v, Type t v) (Term t v)
  CheckSpine      :: (IsVar v)
                  => Ctx t v -> [A.Elim]
                  -> TypeCheckProblem t (Term t v, Type t v) (Term t v, Type t v)
  CheckEqual      :: (IsVar v)
                  => Ctx t v -> Type t v -> Term t v -> Term t v
                  -> TypeCheckProblem t () ()
  CheckEqualSpine :: (IsVar v)
                  => Ctx t v
                  -> [Elim (Term t) v] -> [Elim (Term t) v]
                  -> TypeCheckProblem t (Term t v, Type t v) ()

  MatchPi     :: (IsVar v)
              => Name -> Type t v
              -> (Type t v -> Abs (Type t) v -> StuckTC' t a)
              -> TypeCheckProblem t () a
  MatchEqual  :: (IsVar v)
              => Type t v
              -> (Type t v -> Term t v -> Term t v -> StuckTC' t a)
              -> TypeCheckProblem t () a
  MatchTyCon  :: (IsVar v)
              => Name -> Type t v
              -> ([Term t v] -> StuckTC' t a)
              -> TypeCheckProblem t () a

typeCheckProblem
  :: (IsTerm t, Typeable a, Typeable b)
  => TypeCheckProblem t a b -> a -> StuckTC' t b
typeCheckProblem (WaitingOn f) x =
  returnStuckTC $ f x
typeCheckProblem (CheckEqual1 ctx type_ t1) t2 =
  checkEqual ctx type_ t1 t2
typeCheckProblem (CheckEqualInfer ctx type_) (t, type') = do
  checkEqual ctx set type_ type' `bindStuckTC` WaitingOn (\() -> t)
typeCheckProblem (CheckSpine ctx els) (h', type') = do
  checkSpine ctx h' els type'
typeCheckProblem (CheckEqual ctx type_ x y) () = do
  checkEqual ctx type_ x y
typeCheckProblem (CheckEqualSpine ctx elims1 elims2) (h', type') = do
  checkEqualSpine ctx type' h' elims1 elims2
typeCheckProblem (MatchPi n type_ handler) () =
  matchPi n type_ handler
typeCheckProblem (MatchEqual type_ handler) () =
  matchEqual type_ handler
typeCheckProblem (MatchTyCon n type_ handler) () =
  matchTyCon n type_ handler

metaVarIfStuck
  :: (IsTerm t, IsVar v)
  => Ctx t v -> Type t v -> StuckTC' t (Term t v)
  -> TC' t (Term t v)
metaVarIfStuck ctx type_ m = do
    stuck <- m
    case stuck of
      NotStuck t ->
        return t
      StuckOn pid -> do
        mv <- addMetaVarInCtx ctx type_
        void $ bindProblem pid $ CheckEqual1 ctx type_ mv
        return mv

elimStuckTC :: StuckTC' t a -> TC' t a -> TC' t a
elimStuckTC m ifStuck = do
    stuck <- m
    case stuck of
      NotStuck x   -> return x
      StuckOn _pid -> ifStuck

-- Utils
------------------------------------------------------------------------

-- Matching terms
-----------------

matchTyCon
  :: (IsVar v, IsTerm t, Typeable a)
  => Name
  -> Type t v
  -> ([Term t v] -> StuckTC' t a)
  -> StuckTC' t a
matchTyCon tyCon t handler = do
  blockedT <- whnfTC t
  let t' = ignoreBlocking blockedT
  case blockedT of
    NotBlocked _
      | App (Def tyCon') tyConArgs0 <- view t'
      , tyCon == tyCon', Just tyConArgs <- mapM isApply tyConArgs0 -> do
        handler tyConArgs
    MetaVarHead mv _ -> do
      mvType <- getMetaVarType mv
      mvT <- unrollPiTC mvType $ \ctxMvArgs _ -> do
        Constant _ tyConType <- getDefinition tyCon
        tyConParsTel <- unrollPiTC (vacuous tyConType) $ \ctx -> return . Tel.idTel ctx
        tyConPars <- createMvsPars ctxMvArgs tyConParsTel
        return $ ctxLam ctxMvArgs $ def tyCon $ map Apply tyConPars
      instantiateMetaVar mv mvT
      -- TODO Dangerous recursion, relying on correct instantiation.
      -- Maybe remove and do it explicitly?
      matchTyCon tyCon t' handler
    BlockedOn mvs _ _ -> do
      newProblem mvs (MatchTyCon tyCon t' handler)
    _ -> do
      checkError $ DataConTypeError tyCon t'

matchPi
  :: (IsVar v, IsTerm t, Typeable a)
  => Name                       -- ^ Name for the bound var in the codomain.
  -> Type t v
  -> (Type t v -> Abs (Type t) v -> StuckTC' t a)
  -> StuckTC' t a
matchPi name t handler = do
  blockedT <- whnfTC t
  let t' = ignoreBlocking blockedT
  case blockedT of
    NotBlocked _ | Pi dom cod <- view t'  -> do
      handler dom cod
    MetaVarHead mv _ -> do
      mvType <- getMetaVarType mv
      mvT <- unrollPiTC mvType $ \ctxMvArgs _ -> do
        dom <- addMetaVarInCtx ctxMvArgs set
        cod <- addMetaVarInCtx (Ctx.Snoc ctxMvArgs (name, dom)) set
        return $ ctxLam ctxMvArgs $ pi dom $ toAbs cod
      instantiateMetaVar mv mvT
      -- TODO Dangerous recursion, relying on correct instantiation.
      -- Maybe remove and do it explicitly?
      matchPi name t' handler
    BlockedOn mvs _ _ -> do
      newProblem mvs (MatchPi name t' handler)
    _ ->
      checkError $ ExpectedFunctionType t Nothing

matchPi_
  :: (IsVar v, IsTerm t, Typeable a)
  => Type t v
  -> (Type t v -> Abs (Type t) v -> StuckTC' t a)
  -> StuckTC' t a
matchPi_ = matchPi "_"

matchEqual
  :: (IsVar v, IsTerm t, Typeable a)
  => Type t v
  -> (Type t v -> Term t v -> Term t v -> StuckTC' t a)
  -> StuckTC' t a
matchEqual t handler = do
  blockedT <- whnfTC t
  let t' = ignoreBlocking blockedT
  case blockedT of
    NotBlocked _ | Equal type_ t1 t2 <- view t' -> do
      handler type_ t1 t2
    MetaVarHead mv _ -> do
      mvType <- getMetaVarType mv
      mvT <- unrollPiTC mvType $ \ctxMvArgs _ -> do
        type_ <- addMetaVarInCtx ctxMvArgs set
        t1 <- addMetaVarInCtx ctxMvArgs type_
        t2 <- addMetaVarInCtx ctxMvArgs type_
        return $ ctxLam ctxMvArgs $ equal type_ t1 t2
      instantiateMetaVar mv mvT
      matchEqual t' handler
    BlockedOn mvs _ _ ->
      newProblem mvs (MatchEqual t' handler)
    _ -> do
      checkError $ ExpectedEqual t

applyProjection
  :: (IsVar v, IsTerm t)
  => Name
  -- ^ Name of the projection
  -> Term t v
  -- ^ Head
  -> Type t v
  -- ^ Type of the head
  -> StuckTC' t (Term t v, Type t v)
applyProjection proj h type_ = do
  projDef <- getDefinition proj
  case projDef of
    Projection projIx tyCon projType -> do
      let h' = eliminate h [Proj proj projIx]
      matchTyCon tyCon type_ $ \tyConArgs -> do
        let appliedProjType = view $ Tel.substs (vacuous projType) tyConArgs
        case appliedProjType of
          Pi _ endType ->
            returnStuckTC (h', instantiate endType h)
          _ ->
            error $ "impossible.applyProjection: " ++ render appliedProjType
    _ ->
      error $ "impossible.applyProjection: " ++ render projDef

instantiateDataCon
  :: (IsTerm t)
  => MetaVar
  -> Name
  -- ^ Name of the datacon
  -> TC' t (Closed (Term t))
instantiateDataCon mv dataCon = do
  mvType <- getMetaVarType mv
  mvT <- unrollPiTC mvType $ \ctxMvArgs endType' -> do
    DataCon tyCon dataConTypeTel <- getDefinition dataCon
    -- We know that the metavariable must have the right type (we have
    -- typechecked the arguments already).
    App (Def tyCon') tyConArgs0 <- whnfViewTC endType'
    Just tyConArgs <- return $ mapM isApply tyConArgs0
    True <- return $ tyCon == tyCon'
    let dataConType = Tel.substs (vacuous dataConTypeTel) tyConArgs
    dataConArgsTel <- unrollPiTC dataConType $ \ctx -> return . Tel.idTel ctx
    dataConArgs <- createMvsPars ctxMvArgs dataConArgsTel
    return $ ctxLam ctxMvArgs $ con dataCon $ dataConArgs
  instantiateMetaVar mv mvT
  return mvT

-- Whnf'ing and view'ing
------------------------

whnfTC :: (IsVar v, IsTerm t) => t v -> TC t v' (Blocked t v)
whnfTC t = withSignature $ \sig -> whnf sig t

whnfViewTC :: (IsVar v, IsTerm t) => t v -> TC t v' (TermView t v)
whnfViewTC t = view . ignoreBlocking <$> whnfTC t

-- Unrolling Pis
----------------

-- TODO remove duplication

unrollPiWithNames
  :: (IsVar v, IsTerm t)
  => Sig.Signature t
  -> Type t v
  -- ^ Type to unroll
  -> [Name]
  -- ^ Names to give to each parameter
  -> (∀ v'. (IsVar v') => Ctx.Ctx v (Type t) v' -> Type t v' -> a)
  -- ^ Handler taking a context with accumulated domains of the pis
  -- and the final codomain.
  -> Either (CheckError t) a
unrollPiWithNames _ type_ [] ret =
  Right $ ret Ctx.Empty type_
unrollPiWithNames sig type_ (name : names) ret =
  case whnfView sig type_ of
    Pi domain codomain ->
      unrollPiWithNames sig (fromAbs codomain) names $ \ctxVs endType ->
      ret (Ctx.singleton name domain Ctx.++ ctxVs) endType
    _ ->
      Left $ ExpectedFunctionType type_ Nothing

unrollPiWithNamesTC
  :: (IsVar v, IsTerm t) => Type t v -> [Name]
  -> (∀ v'. (IsVar v') => Ctx.Ctx v (Type t) v' -> Type t v' -> TC t p a)
  -> TC t p a
unrollPiWithNamesTC type_ names ret = do
  errOrM <- withSignature $ \sig -> unrollPiWithNames sig type_ names ret
  case errOrM of
    Left err -> checkError err
    Right m  -> m

unrollPi
  :: (IsVar v, IsTerm t)
  => Sig.Signature t
  -> Type t v
  -- ^ Type to unroll
  -> (∀ v'. (IsVar v') => Ctx.Ctx v (Type t) v' -> Type t v' -> a)
  -- ^ Handler taking a weakening function, the list of domains
  -- of the unrolled pis, the final codomain.
  -> a
unrollPi sig type_ ret = do
  case whnfView sig type_ of
    Pi domain codomain ->
      let codomain' = fromAbs codomain
          name      = getName_ codomain'
      in unrollPi sig codomain' $ \ctxVs endType ->
         ret (Ctx.singleton name domain Ctx.++ ctxVs) endType
    _ ->
      ret Ctx.Empty type_

unrollPiTC
  :: (IsVar v, IsTerm t)
  => Type t v
  -> (∀ v'. (IsVar v') => Ctx.Ctx v (Type t) v' -> Type t v' -> TC t p a)
  -> TC t p a
unrollPiTC type_ ret = do
  join $ withSignature $ \sig -> unrollPi sig type_ ret

-- Errors
---------

data CheckError t
    = ∀ v. (IsVar v) => DataConTypeError Name (Type t v)
    | ∀ v. (IsVar v) => LambdaTypeError A.Expr (Type t v)
    | ∀ v. (IsVar v) => NotEqualityType (Type t v)
    | ∀ v. (IsVar v) => ExpectedFunctionType (Type t v) (Maybe A.Expr)
    | CannotInferTypeOf A.Expr
    | ∀ v. (IsVar v) => TermsNotEqual (Term t v) (Term t v)
    | ∀ v. (IsVar v) => SpineNotEqual (Type t v) [Elim t v] [Elim t v]
    | ∀ v. (IsVar v) => ExpectingRecordType (Type t v)
    | ∀ v. (IsVar v) => FreeVariableInEquatedTerm MetaVar [Elim t v] (Term t v) v
    | PatternMatchOnRecord A.Pattern
                           Name -- Record type constructor
    | ∀ v. (IsVar v) => MismatchingPattern (Type t v) A.Pattern
    | OccursCheckFailed MetaVar (Closed (Term t))
    | ∀ v. (IsVar v) => ExpectedEqual (Term t v)
    | NameNotInScope Name
    | StuckTypeSignature Name
    | ClausesAlreadyAdded Name

checkError :: (IsTerm t) => CheckError t -> TC t p a
checkError err = do
  doc <- withSignature $ \sig -> renderError sig err
  typeError doc

renderError :: forall t. (IsTerm t) => Sig.Signature t -> CheckError t -> PP.Doc
renderError sig term0 = case term0 of
  DataConTypeError synT type_ ->
    "DataCon type error" $$
    PP.nest 2 (PP.pretty synT $$ PP.nest 2 ":" $$ prettyTerm type_)
  NotEqualityType type_ ->
    "Expecting an equality type:" $$ PP.nest 2 (prettyTerm type_)
  LambdaTypeError synT type_ ->
    "Lambda type error:" $$
    PP.nest 2 (PP.pretty synT $$ PP.nest 2 ":" $$ prettyTerm type_)
  ExpectedFunctionType type_ mbArg ->
    "Expected function type:" $$ PP.nest 2 (prettyTerm type_) $$
    (case mbArg of
       Nothing  -> ""
       Just arg -> "In application of" $$ PP.nest 2 (PP.pretty arg))
  CannotInferTypeOf synT ->
    "Cannot infer type of:" $$ PP.pretty synT
  TermsNotEqual t1 t2 ->
    prettyTerm t1 $$ PP.nest 2 "!=" $$ prettyTerm t2
  SpineNotEqual type_ es1 es2 ->
    PP.pretty es1 $$ PP.nest 2 "!=" $$
    PP.pretty es2 $$ PP.nest 2 ":" $$
    prettyTerm type_
  ExpectingRecordType type_ ->
    "Expecting record type:" $$ PP.nest 2 (prettyTerm type_)
  FreeVariableInEquatedTerm mv els rhs v ->
    "Free variable `" <> prettyVar v <> "' in term equated to metavariable application:" $$
    prettyTerm (metaVar mv els) $$
    PP.nest 2 "=" $$
    prettyTerm rhs
  PatternMatchOnRecord synPat tyCon ->
    "Cannot have pattern" <+> PP.pretty synPat <+> "for record type" <+> PP.pretty tyCon
  MismatchingPattern type_ synPat ->
    PP.pretty synPat <+> "does not match an element of type" $$ prettyTerm type_
  OccursCheckFailed mv t ->
    "Attempt at recursive instantiation:" $$
    PP.pretty mv <+> ":=" <+> prettyTerm t
  ExpectedEqual type_ ->
    "Expected identity type:" $$
    PP.nest 2 (prettyTerm type_)
  NameNotInScope name ->
    "Name not in scope:" <+> PP.pretty name
  StuckTypeSignature name ->
    "Got stuck on the type signature when checking clauses for function `" <> PP.pretty name <> "'"
  ClausesAlreadyAdded fun ->
    "Clauses already added for function `" <> PP.pretty fun <> "'"
  where
    prettyVar :: forall v. (IsVar v) => v -> PP.Doc
    prettyVar = PP.pretty . varName

    prettyTerm :: forall v. (IsVar v) => t v -> PP.Doc
    prettyTerm = PP.pretty . view . instantiateMetaVars sig

instantiateMetaVars :: (IsVar v, IsTerm t) => Sig.Signature t -> t v -> t v
instantiateMetaVars sig t = unview $
  case view t of
    Lam abs ->
      Lam (goAbs abs)
    Pi dom cod ->
      Pi (go dom) (goAbs cod)
    Equal type_ x y ->
      Equal (go type_) (go x) (go y)
    Refl ->
      Refl
    Con dataCon ts ->
      Con dataCon $ map go ts
    Set ->
      Set
    App (Meta mv) els | Just t' <- Sig.getMetaVarBody sig mv ->
      view $ instantiateMetaVars sig $ eliminate (vacuousM t') els
    App h els ->
      App h $ map goElim els
  where
    go = instantiateMetaVars sig

    goAbs = toAbs . instantiateMetaVars sig . fromAbs

    goElim (Proj n field) = Proj n field
    goElim (Apply t')     = Apply (go t')


-- Clauses invertibility
------------------------

termHead :: (IsTerm t) => Sig.Signature t -> t v -> Maybe TermHead
termHead sig t = case whnfView sig t of
  App (Def f) _ ->
    case Sig.getDefinition sig f of
      Constant Data{}      _ -> Just $ DefHead f
      Constant Record{}    _ -> Just $ DefHead f
      -- TODO here we can't return 'Just' because we don't know if the
      -- postulate is going to be instantiated afterwards.  Ideally we'd
      -- have a "postulate" keyword to avoid this.
      Constant Postulate{} _ -> Nothing
      _                      -> Nothing
  Con f _ ->
    Just $ DefHead f
  Pi _ _ ->
    Just $ PiHead
  _ ->
    Nothing

checkInvertibility
  :: (IsTerm t) => Sig.Signature t -> [Closed (Clause t)] -> Closed (Invertible t)
checkInvertibility sig = go []
  where
    go injClauses [] =
      Invertible $ reverse injClauses
    go injClauses (clause@(Clause _ body) : clauses) =
      case termHead sig (fromScope body) of
        Just tHead | Nothing <- lookup tHead injClauses ->
          go ((tHead, clause) : injClauses) clauses
        _ ->
          NotInvertible $ reverse (map snd injClauses) ++ (clause : clauses)

-- Telescope & context utils
----------------------------

telPi :: (IsVar v, IsTerm t) => Tel.IdTel (Type t) v -> Type t v
telPi tel = Tel.unTel tel $ \ctx endType -> ctxPi ctx (Tel.unId endType)

-- | Collects all the variables in the 'Ctx.Ctx'.
ctxVars :: IsTerm t => Ctx.Ctx v0 (Type t) v -> [v]
ctxVars = reverse . go
  where
    go :: IsTerm t => Ctx.Ctx v0 (Type t) v -> [v]
    go Ctx.Empty                = []
    go (Ctx.Snoc ctx (name, _)) = boundTermVar name : map F (go ctx)

-- | Applies a 'Term' to all the variables in the context.  The
-- variables are applied from left to right.
ctxApp :: (IsVar v, IsTerm t) => Term t v -> Ctx.Ctx v0 (Type t) v -> Term t v
ctxApp t ctx0 = eliminate t $ map (Apply . var) $ ctxVars ctx0

-- | Creates a 'Pi' type containing all the types in the 'Ctx' and
-- terminating with the provided 't'.
ctxPi :: IsTerm t => Ctx.Ctx v0 (Type t) v -> Type t v -> Type t v0
ctxPi Ctx.Empty                  t = t
ctxPi (Ctx.Snoc ctx (_n, type_)) t = ctxPi ctx $ pi type_ (toAbs t)

-- | Creates a 'Lam' term with as many arguments there are in the
-- 'Ctx.Ctx'.
ctxLam :: IsTerm t => Ctx.Ctx v0 (Type t) v -> Term t v -> Term t v0
ctxLam Ctx.Empty        t = t
ctxLam (Ctx.Snoc ctx _) t = ctxLam ctx $ lam $ toAbs t

-- Miscellanea
--------------

isApply :: Elim (Term t) v -> Maybe (Term t v)
isApply (Apply v) = Just v
isApply Proj{}    = Nothing

definitionType :: (IsTerm t) => Closed (Definition t) -> Closed (Type t)
definitionType (Constant _ type_)   = type_
definitionType (DataCon _ tel)      = telPi tel
definitionType (Projection _ _ tel) = telPi tel
definitionType (Function type_ _)   = type_

isRecordType :: (IsTerm t) => Sig.Signature t -> Name -> Bool
isRecordType sig tyCon =
  case Sig.getDefinition sig tyCon of
    Constant (Record _ _) _ -> True
    _                       -> False

isRecordConstr :: (IsTerm t) => Sig.Signature t -> Name -> Bool
isRecordConstr sig dataCon =
  case Sig.getDefinition sig dataCon of
    DataCon tyCon _ -> isRecordType sig tyCon
    _               -> False
