{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OverloadedStrings #-}
module TypeCheck3.Check (CheckState, initCheckState, checkDecl) where

import           Prelude                          hiding (abs, pi)

import qualified Control.Lens                     as L

import           Prelude.Extended
import           Syntax.Internal                  (Name)
import qualified Syntax.Internal                  as A
import           Term
import           Term.Context                     (Ctx)
import qualified Term.Context                     as Ctx
import qualified Term.Telescope                   as Tel
import           PrettyPrint                      (($$), (//>), render)
import qualified PrettyPrint                      as PP
import           TypeCheck3.Monad
import           TypeCheck3.Core
import           TypeCheck3.Common
import           TypeCheck3.Elaborate
import           TypeCheck3.Solve

-- Decls
------------------------------------------------------------------------

data CheckState t = CheckState
  { _csSolveState     :: !(SolveState t)
  , _csElaborateState :: !ElaborateState
  }

L.makeLenses ''CheckState

initCheckState :: CheckState t
initCheckState = CheckState initSolveState initElaborateState

type CheckM t = TC t (CheckState t)

checkDecl :: (IsTerm t) => A.Decl -> CheckM t ()
checkDecl decl = do
  debugBracket_ ("*** checkDecl" $$ PP.pretty decl) $ atSrcLoc decl $ do
    case decl of
      A.TypeSig sig      -> checkTypeSig sig
      A.DataDef d xs cs  -> checkData d xs cs
      A.RecDef d xs c fs -> checkRec d xs c fs
      A.FunDef f clauses -> checkFunDef f clauses

elaborateAndCheck
  :: (IsTerm t)
  => Ctx t -> A.Expr -> Type t -> CheckM t (Term t)
elaborateAndCheck ctx synT type_ = do
  debugBracket_ "*** elaborateAndCheck" $ do
    (t, constr) <- mapTC csElaborateState $ elaborate ctx type_ synT
    debug $ do
      constrDoc <- prettyConstraintTC constr
      return $ "** Constraint:" //> constrDoc
    mapTC csSolveState $ solve constr
    check ctx t type_
    return t

checkTypeSig :: (IsTerm t) => A.TypeSig -> CheckM t ()
checkTypeSig (A.Sig name absType) = do
    type_ <- elaborateAndCheck Ctx.Empty absType set
    addConstant name Postulate type_

checkData
    :: (IsTerm t)
    => Name
    -- ^ Name of the tycon.
    -> [Name]
    -- ^ Names of parameters to the tycon.
    -> [A.TypeSig]
    -- ^ Types for the data constructors.
    -> CheckM t ()
checkData tyCon tyConPars dataCons = do
    tyConType <- definitionType =<< getDefinition tyCon
    addConstant tyCon (Data []) tyConType
    (tyConPars', endType) <- unrollPiWithNames tyConType tyConPars
    checkEqual (tyConPars', set, endType, set)
    appliedTyConType <- ctxAppTC (def tyCon []) tyConPars'
    mapM_ (checkConstr tyCon tyConPars' appliedTyConType) dataCons

checkConstr
    :: (IsTerm t)
    => Name
    -- ^ Name of the tycon.
    -> Ctx (Type t)
    -- ^ Ctx with the parameters of the tycon.
    -> Type t
    -- ^ Tycon applied to the parameters.
    -> A.TypeSig
    -- ^ Data constructor.
    -> CheckM t ()
checkConstr tyCon tyConPars appliedTyConType (A.Sig dataCon synDataConType) = do
  atSrcLoc dataCon $ do
    dataConType <- elaborateAndCheck tyConPars synDataConType set
    (vs, endType) <- unrollPi dataConType
    appliedTyConType' <- liftTermM $ Ctx.weaken_ vs appliedTyConType
    let ctx = tyConPars Ctx.++ vs
    checkEqual (ctx, set, appliedTyConType', endType)
    addDataCon dataCon tyCon (Tel.tel tyConPars) dataConType

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
    -> CheckM t ()
checkRec tyCon tyConPars dataCon fields = do
    tyConType <- definitionType =<< getDefinition tyCon
    addConstant tyCon (Record dataCon []) tyConType
    (tyConPars', endType) <- unrollPiWithNames tyConType tyConPars
    checkEqual (tyConPars', set, endType, set)
    fieldsTel <- checkFields tyConPars' fields
    appliedTyConType <- ctxAppTC (def tyCon []) tyConPars'
    fieldsTel' <- liftTermM $ Tel.weaken_ 1 fieldsTel
    addProjections
      tyCon tyConPars' (boundVar "_") (map A.typeSigName fields)
      fieldsTel'
    let fieldsCtx = Tel.unTel fieldsTel
    appliedTyConType' <- liftTermM $ Ctx.weaken_ fieldsCtx appliedTyConType
    addDataCon dataCon tyCon (Tel.tel tyConPars') =<< ctxPiTC fieldsCtx appliedTyConType'

checkFields
    :: forall t. (IsTerm t)
    => Ctx t -> [A.TypeSig] -> CheckM t (Tel.Tel (Type t))
checkFields ctx0 = go Ctx.Empty
  where
    go :: Ctx.Ctx (Type t) -> [A.TypeSig] -> CheckM t (Tel.Tel (Type t))
    go ctx [] =
        return $ Tel.tel ctx
    go ctx (A.Sig field synFieldType : fields) = do
        fieldType <- elaborateAndCheck (ctx0 Ctx.++ ctx) synFieldType set
        ctx' <- extendContext ctx (field, fieldType)
        go ctx' fields

addProjections
    :: (IsTerm t)
    => Name
    -- ^ Type constructor.
    -> Ctx (Type t)
    -- ^ A context with the parameters to the type constructor.
    -> Var
    -- ^ Variable referring to the value of type record type itself,
    -- which is the last argument of each projection ("self").  Note
    -- that this variable will have all the context above in scope.
    -> [Name]
    -- ^ Names of the remaining fields.
    -> Tel.Tel (Type t)
    -- ^ Telescope holding the types of the next fields, scoped
    -- over the types of the previous fields and the self variable.
    -> CheckM t ()
addProjections tyCon tyConPars self fields0 =
    go $ zip fields0 $ map Field [0,1..]
  where
    go fields fieldTypes = case (fields, fieldTypes) of
      ([], Tel.Empty) ->
        return ()
      ((field, ix) : fields', Tel.Cons (_, fieldType) fieldTypes') -> do
        endType <- (`piTC` fieldType) =<< ctxAppTC (def tyCon []) tyConPars
        addProjection field ix tyCon (Tel.tel tyConPars) endType
        (go fields' <=< liftTermM . Tel.instantiate fieldTypes') =<< appTC (Var self) [Proj field ix]
      (_, _) -> fatalError "impossible.addProjections: impossible: lengths do not match"

checkFunDef :: (IsTerm t) => Name -> [A.Clause] -> CheckM t ()
checkFunDef fun synClauses = do
    funType <- definitionType =<< getDefinition fun
    clauses <- mapM (checkClause fun funType) synClauses
    inv <- checkInvertibility clauses
    addClauses fun inv

checkClause
  :: (IsTerm t)
  => Name -> Closed (Type t)
  -> A.Clause
  -> CheckM t (Closed (Clause t))
checkClause fun funType (A.Clause synPats synClauseBody) = do
  (ctx, pats, _, clauseType) <- checkPatterns fun synPats funType
  let msg = do
        ctxDoc <- prettyContextTC ctx
        return $ "*** checkClause" $$
                 "context:" //> ctxDoc
  debugBracket msg $ do
    clauseBody <- elaborateAndCheck ctx synClauseBody clauseType
    -- This is an optimization: we want to remove as many MetaVars
    -- as possible so that we'll avoid recomputing things.
    -- TODO generalize this to everything which adds a term.
    clauseBody' <- withSignatureTermM $ \sig -> instantiateMetaVars sig clauseBody
    return $ Clause pats clauseBody'

checkPatterns
  :: (IsTerm t)
  => Name
  -> [A.Pattern]
  -> Type t
  -- ^ Type of the clause that has the given 'A.Pattern's in front.
  -> CheckM t (Ctx (Type t), [Pattern], [Term t], Type t)
  -- ^ A context into the internal variables, list of internal patterns,
  -- a list of terms produced by their bindings, and the type of the
  -- clause body (scoped over the pattern variables).
checkPatterns _ [] type_ =
    return (Ctx.Empty, [], [], type_)
checkPatterns funName (synPat : synPats) type0 = atSrcLoc synPat $ do
  -- TODO this can be a soft match, like `matchPi'.  I just need to
  -- carry the context around.
  typeView <- whnfViewTC type0
  case typeView of
    Pi dom cod -> do
      (ctx, pat, patVar) <- checkPattern funName synPat dom
      cod'  <- liftTermM $ Ctx.weaken 1 ctx cod
      cod'' <- instantiateTC cod' patVar
      (ctx', pats, patsVars, bodyType) <- checkPatterns funName synPats cod''
      patVar' <- liftTermM $ Ctx.weaken_ ctx' patVar
      return (ctx Ctx.++ ctx', pat : pats, patVar' : patsVars, bodyType)
    _ -> do
      checkError $ ExpectingPi type0

checkPattern
    :: (IsTerm t)
    => Name
    -> A.Pattern
    -> Type t
    -- ^ Type of the matched thing.
    -> CheckM t (Ctx (Type t), Pattern, Term t)
    -- ^ The context, the internal 'Pattern', and a 'Term' containing
    -- the term produced by it.
checkPattern funName synPat type_ = case synPat of
    A.VarP name -> do
      v <- varTC $ boundVar name
      return (Ctx.singleton name type_, VarP, v)
    A.WildP _ -> do
      v <- varTC $ boundVar "_"
      return (Ctx.singleton "_" type_, VarP, v)
    A.ConP dataCon synPats -> do
      DataCon tyCon tyConParsTel dataConType <- getDefinition dataCon
      typeConDef <- getDefinition tyCon
      case typeConDef of
        Constant (Data _)     _ -> return ()
        Constant (Record _ _) _ -> checkError $ PatternMatchOnRecord synPat tyCon
        _                       -> do doc <- prettyDefinitionTC typeConDef
                                      fatalError $ "impossible.checkPattern " ++ render doc
      typeView <- whnfViewTC type_
      -- TODO this can be a soft match, like `matchTyCon'
      case typeView of
        App (Def tyCon') tyConArgs0 | tyCon == tyCon' -> do
          let Just tyConArgs = mapM isApply tyConArgs0
          dataConTypeNoPars <- liftTermM $ Tel.substs tyConParsTel dataConType tyConArgs
          (ctx, pats, patsVars, _) <- checkPatterns funName synPats dataConTypeNoPars
          t <- conTC dataCon patsVars
          return (ctx, ConP dataCon pats, t)
        _ -> do
          checkError $ ExpectingTyCon tyCon type_
