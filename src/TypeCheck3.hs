{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
-- TODO add options that are present in TypeCheck
module TypeCheck3
  ( -- * Global state
    TCState'
  , -- * Program checking
    checkProgram
    -- * Interactive mode
  , Command
  , parseCommand
  , runCommand
  ) where

import           Prelude                          hiding (abs, pi)

import           Control.Lens                     ((^.))
import qualified Control.Lens                     as L
import           Control.Monad.Trans.Except       (ExceptT(ExceptT), runExceptT, throwE)
import           Data.Proxy                       (Proxy(Proxy))
import qualified Data.HashSet                     as HS
import qualified Data.HashMap.Strict              as HMS
import qualified Text.ParserCombinators.ReadP     as ReadP

import           Conf
import           Prelude.Extended
import           Syntax.Internal                  (Name)
import qualified Syntax.Internal                  as A
import           Syntax.Raw                       (parseExpr)
import           Term
import qualified Term.Signature                   as Sig
import           Term.Context                     (Ctx)
import qualified Term.Context                     as Ctx
import qualified Term.Telescope                   as Tel
import           Term.Impl
import           PrettyPrint                      ((<+>), render, (//>), ($$))
import qualified PrettyPrint                      as PP
import           TypeCheck3.Monad
import           TypeCheck3.Check
import           TypeCheck3.Common
import           TypeCheck3.Elaborate
import           TypeCheck3.Solve

-- Type checking
------------------------------------------------------------------------

data CheckState t = CheckState
  { _csSolveState     :: !(SolveState t)
  , _csElaborateState :: !(ElaborateState t)
  }

L.makeLenses ''CheckState

initCheckState :: (IsTerm t) => IO (CheckState t)
initCheckState = CheckState <$> initSolveState <*> initElaborateState

type CheckM t = TC t (CheckState t)

-- Decls
------------------------------------------------------------------------

checkDecl :: (IsTerm t) => A.Decl -> CheckM t ()
checkDecl decl = do
  debugBracket_ ("*** checkDecl" $$ PP.pretty decl) $ atSrcLoc decl $ do
    case decl of
      A.TypeSig sig      -> checkTypeSig sig
      A.DataDef d xs cs  -> checkData d xs cs
      A.RecDef d xs c fs -> checkRec d xs c fs
      A.FunDef f clauses -> checkFunDef f clauses

inferExpr
  :: (IsTerm t)
  => Ctx t -> A.Expr -> CheckM t (Term t, Type t)
inferExpr ctx synT = do
  type_ <- addMetaVarInCtx ctx set
  t <- checkExpr ctx synT type_
  return (t, type_)

checkExpr
  :: (IsTerm t)
  => Ctx t -> A.Expr -> Type t -> CheckM t (Term t)
checkExpr ctx synT type_ = do
  debugBracket_ "*** checkExpr" $ do
    (t, constr) <- mapTC csElaborateState $ elaborate ctx type_ synT
    debug $ do
      constrDoc <- prettyM constr
      return $ "** Constraint:" //> constrDoc
    mapTC csSolveState $ solve constr
    check ctx t type_
    return t

checkTypeSig :: (IsTerm t) => A.TypeSig -> CheckM t ()
checkTypeSig (A.Sig name absType) = do
    type_ <- checkExpr Ctx.Empty absType set
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
    definitionallyEqual tyConPars' set endType set
    appliedTyConType <- Ctx.app (def tyCon []) tyConPars'
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
    dataConType <- checkExpr tyConPars synDataConType set
    (vs, endType) <- unrollPi dataConType
    appliedTyConType' <- Ctx.weaken_ vs appliedTyConType
    let ctx = tyConPars Ctx.++ vs
    definitionallyEqual ctx set appliedTyConType' endType
    addDataCon dataCon tyCon (Ctx.length vs) (Tel.tel tyConPars) dataConType

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
    definitionallyEqual tyConPars' set endType set
    fieldsTel <- checkFields tyConPars' fields
    appliedTyConType <- Ctx.app (def tyCon []) tyConPars'
    fieldsTel' <- Tel.weaken_ 1 fieldsTel
    addProjections
      tyCon tyConPars' (boundVar "_") (map A.typeSigName fields)
      fieldsTel'
    let fieldsCtx = Tel.unTel fieldsTel
    appliedTyConType' <- Ctx.weaken_ fieldsCtx appliedTyConType
    addDataCon dataCon tyCon (length fields) (Tel.tel tyConPars') =<< Ctx.pi fieldsCtx appliedTyConType'

checkFields
    :: forall t. (IsTerm t)
    => Ctx t -> [A.TypeSig] -> CheckM t (Tel.Tel (Type t))
checkFields ctx0 = go Ctx.Empty
  where
    go :: Ctx.Ctx (Type t) -> [A.TypeSig] -> CheckM t (Tel.Tel (Type t))
    go ctx [] =
        return $ Tel.tel ctx
    go ctx (A.Sig field synFieldType : fields) = do
        fieldType <- checkExpr (ctx0 Ctx.++ ctx) synFieldType set
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
        endType <- (`pi` fieldType) =<< Ctx.app (def tyCon []) tyConPars
        addProjection field ix tyCon (Tel.tel tyConPars) endType
        (go fields' <=< Tel.instantiate fieldTypes') =<< app (Var self) [Proj field ix]
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
        ctxDoc <- prettyM ctx
        return $ "*** checkClause" $$
                 "context:" //> ctxDoc
  debugBracket msg $ do
    clauseBody <- checkExpr ctx synClauseBody clauseType
    -- This is an optimization: we want to remove as many MetaVars
    -- as possible so that we'll avoid recomputing things.
    -- TODO generalize this to everything which adds a term.
    clauseBody' <- instantiateMetaVars clauseBody
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
  typeView <- whnfView type0
  case typeView of
    Pi dom cod -> do
      (ctx, pat, patVar) <- checkPattern funName synPat dom
      cod'  <- Ctx.weaken 1 ctx cod
      cod'' <- instantiate cod' patVar
      (ctx', pats, patsVars, bodyType) <- checkPatterns funName synPats cod''
      patVar' <- Ctx.weaken_ ctx' patVar
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
      v <- var $ boundVar name
      return (Ctx.singleton name type_, VarP, v)
    A.WildP _ -> do
      v <- var $ boundVar "_"
      return (Ctx.singleton "_" type_, VarP, v)
    A.ConP dataCon synPats -> do
      DataCon tyCon _ tyConParsTel dataConType <- getDefinition dataCon
      typeConDef <- getDefinition tyCon
      case typeConDef of
        Constant (Data _)     _ -> return ()
        Constant (Record _ _) _ -> checkError $ PatternMatchOnRecord synPat tyCon
        _                       -> do doc <- prettyM typeConDef
                                      fatalError $ "impossible.checkPattern " ++ render doc
      typeView <- whnfView type_
      -- TODO this can be a soft match, like `matchTyCon'
      case typeView of
        App (Def tyCon') tyConArgs0 | tyCon == tyCon' -> do
          let Just tyConArgs = mapM isApply tyConArgs0
          dataConTypeNoPars <- Tel.substs tyConParsTel dataConType tyConArgs
          (ctx, pats, patsVars, _) <- checkPatterns funName synPats dataConTypeNoPars
          t <- con dataCon patsVars
          return (ctx, ConP dataCon pats, t)
        _ -> do
          checkError $ ExpectingTyCon tyCon type_

-- Bringing everything together
------------------------------------------------------------------------

-- Checking programs
--------------------

type TCState' t = TCState t (CheckState t)

checkProgram
  :: [A.Decl]
  -> (forall t. (IsTerm t) => Either PP.Doc (TCState' t) -> IO a) -> IO a
checkProgram decls ret = do
  tt <- confTermType <$> readConf
  case tt of
    "S"  -> checkProgram' (Proxy :: Proxy Simple)      decls ret
    "GR" -> checkProgram' (Proxy :: Proxy GraphReduce) decls ret
    -- "EW" -> checkProgram' (Proxy :: Proxy EasyWeaken)  decls cmds ret
    "H"  -> checkProgram' (Proxy :: Proxy Hashed)      decls ret
    -- "SUSP" -> checkProgram' (Proxy :: Proxy Suspension) decls cmds ret
    type_ -> ret (Left ("Invalid term type" <+> PP.text type_) :: Either PP.Doc (TCState' Simple))

checkProgram'
    :: forall t a. (IsTerm t)
    => Proxy t -> [A.Decl] -> (Either PP.Doc (TCState' t) -> IO a) -> IO a
checkProgram' _ decls0 ret = do
    quiet <- confQuiet <$> readConf
    unless quiet $ do
      drawLine
      putStrLn "-- Checking declarations"
      drawLine
    s <- initCheckState
    ret =<< runExceptT (goDecls (initTCState s) decls0)
  where
    goDecls :: TCState' t -> [A.Decl] -> ExceptT PP.Doc IO (TCState' t)
    goDecls ts [] = do
      ts <$ checkState ts
    goDecls ts (decl : decls) = do
      quiet <- confQuiet <$> readConf
      cdebug <- confDebug <$> readConf
      unless quiet $ lift $ do
        putStrLn $ render decl
        let separate = case decl of
              A.TypeSig (A.Sig n _) -> case decls of
                A.FunDef n' _     : _  -> not $ n == n'
                A.DataDef n' _ _  : _  -> not $ n == n'
                A.RecDef n' _ _ _ : _  -> not $ n == n'
                []                     -> False
                _                      -> True
              _ ->
                not $ null decls
        when separate $ putStrLn ""
      ((), ts') <- ExceptT $ runTC (not quiet && cdebug) ts $ checkDecl decl
      goDecls ts' decls

    -- TODO change for this to work in TC
    checkState :: TCState' t -> ExceptT PP.Doc IO ()
    checkState ts = do
      let sig = tsSignature ts
      unsolvedMvs <- lift $ runTermM sig $ metaVars' sig
      quiet <- confQuiet <$> readConf
      unless quiet $ lift $ do
        mvNoSummary <- confNoMetaVarsSummary <$> readConf
        mvReport <- confMetaVarsReport <$> readConf
        mvOnlyUnsolved <- confMetaVarsOnlyUnsolved <$> readConf
        when (not mvNoSummary || mvReport) $ do
          let solvedMvs   = HS.fromList $ HMS.keys $ Sig.metaVarsBodies sig
          drawLine
          putStrLn $ "-- Solved MetaVars: " ++ show (HS.size solvedMvs)
          putStrLn $ "-- Unsolved MetaVars: " ++ show (HS.size unsolvedMvs)
          when mvReport $ do
            drawLine
            let mvsTypes = Sig.metaVarsTypes sig
            forM_ (sortBy (comparing fst) $ HMS.toList mvsTypes) $ \(mv, mvType) -> do
              let mbBody = Sig.getMetaVarBody sig mv
              when (not (isJust mbBody) || not mvOnlyUnsolved) $ do
                mvTypeDoc <- runTermM sig $ prettyTermM mvType
                putStrLn $ render $
                  PP.pretty mv <+> PP.parens (PP.pretty (mvSrcLoc mv)) <+> ":" //> mvTypeDoc
                when (not mvOnlyUnsolved) $ do
                  mvBody <- case mbBody of
                    Nothing      -> return "?"
                    Just mvBody0 -> runTermM sig $ prettyTermM mvBody0
                  putStrLn $ render $ PP.pretty mv <+> "=" <+> PP.nest 2 mvBody
                putStrLn ""
        noProblemsSummary <- confNoProblemsSummary <$> readConf
        problemsReport <- confProblemsReport <$> readConf
        when (not noProblemsSummary || problemsReport) $  do
          drawLine
          putStrLn . render =<< runTermM sig (prettyM (tsState ts ^. csSolveState))
        drawLine
      unless (HS.null unsolvedMvs) $ do
        throwE $ "Unsolved metas: " <+> PP.pretty (HS.toList unsolvedMvs)

    drawLine =
      putStrLn "------------------------------------------------------------------------"

-- Commands
------------------------------------------------------------------------

data Command
  = TypeOf A.Expr
  | Normalize A.Expr
  | ShowConstraints
  deriving (Eq, Show)

parseCommand :: TCState' t -> String -> Either PP.Doc Command
parseCommand ts s = runReadP $
  (do void $ ReadP.string ":t "
      return (\s' -> TypeOf <$> parseAndScopeCheck s')) <|>
  (do void $ ReadP.string ":n "
      return (\s' -> Normalize <$> parseAndScopeCheck s')) <|>
  (do void $ ReadP.string ":c"
      ReadP.eof
      return (\_ -> Right ShowConstraints))
  where
    scope = Sig.toScope $ tsSignature ts

    parseAndScopeCheck = parseExpr >=> A.scopeCheckExpr scope

    runReadP :: ReadP.ReadP (String -> Either PP.Doc Command) -> Either PP.Doc Command
    runReadP p = case ReadP.readP_to_S p s of
      []            -> Left "Unrecognised command"
      ((f, s') : _) -> f s'

runCommand :: (IsTerm t) => TCState' t -> Command -> IO (PP.Doc, TCState' t)
runCommand ts cmd =
  case cmd of
    TypeOf synT -> runTC' $ do
      (_, type_) <- inferExpr Ctx.Empty synT
      typeDoc <- prettyTermM type_
      return $ "type:" //> typeDoc
    Normalize synT -> runTC' $ do
      (t, type_) <- inferExpr Ctx.Empty synT
      typeDoc <- prettyTermM type_
      tDoc <- prettyTermM t
      return $
        "type:" //> typeDoc $$
        "term:" //> tDoc
    ShowConstraints -> runTC' $ do
      prettyM =<< L.use csSolveState
  where
    runTC' m = do
      mbErr <- runTC False ts m
      let doc = case mbErr of
                  Left err       -> "Error:" //> err
                  Right (doc0, _) -> doc0
      return (doc, ts)
