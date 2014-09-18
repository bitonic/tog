{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
-- TODO add options that are present in TypeCheck
module TypeCheck3
  ( availableTermTypes
  , checkProgram
  , TCState'
  , Command
  , parseCommand
  , runCommand
  ) where

import           Prelude                          hiding (abs, pi)

import           Control.Lens                     ((^.))
import           Control.Monad.Trans.Except       (ExceptT(ExceptT), runExceptT)
import           Data.Proxy                       (Proxy(Proxy))
import qualified Data.HashMap.Strict              as HMS
import qualified Text.ParserCombinators.ReadP     as ReadP

import           Conf
import           Prelude.Extended
import qualified Syntax.Internal                  as A
import           Syntax.Raw                       (parseExpr)
import           Term
import qualified Term.Signature                   as Sig
import qualified Term.Context                     as Ctx
import           Term.Impl
import           PrettyPrint                      ((<+>), render, (//>), ($$))
import qualified PrettyPrint                      as PP
import           TypeCheck3.Monad
import           TypeCheck3.Check
import           TypeCheck3.Common
import           TypeCheck3.Solve

-- Type checking
------------------------------------------------------------------------

-- Checking programs
--------------------

availableTermTypes :: [String]
availableTermTypes = ["GR", "S", "H", "SUSP"]

type TCState' t = TCState t (CheckState t)

checkProgram
  :: forall a. [A.Decl]
  -> (forall t. (IsTerm t) => Either PP.Doc (TCState' t) -> IO a)
  -> IO a
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
    :: forall t b. (IsTerm t)
    => Proxy t -> [A.Decl]
    -> (forall a. (IsTerm a) => Either PP.Doc (TCState' a) -> IO b)
    -> IO b
checkProgram' _ decls0 ret = do
    quiet <- confQuiet <$> readConf
    unless quiet $ do
      drawLine
      putStrLn "-- Checking declarations"
      drawLine
    let s = initCheckState
    ret =<< runExceptT (goDecls (initTCState s) decls0)
  where
    goDecls :: TCState' t -> [A.Decl] -> ExceptT PP.Doc IO (TCState' t)
    goDecls ts [] = do
      quiet <- confQuiet <$> lift readConf
      lift $ unless quiet  $ report ts
      return ts
    goDecls ts (decl : decls) = do
      quiet <- confQuiet <$> lift readConf
      cdebug <- confDebug <$> lift readConf
      lift $ unless quiet $ do
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
    report :: TCState' t -> IO ()
    report ts = do
      let sig = tsSignature ts
      mvNoSummary <- confNoMetaVarsSummary <$> readConf
      mvReport <- confMetaVarsReport <$> readConf
      mvOnlyUnsolved <- confMetaVarsOnlyUnsolved <$> readConf
      when (not mvNoSummary || mvReport) $ do
        let mvsTypes  = Sig.metaVarsTypes sig
        let mvsBodies = Sig.metaVarsBodies sig
        drawLine
        putStrLn $ "-- Solved MetaVars: " ++ show (HMS.size mvsBodies)
        putStrLn $ "-- Unsolved MetaVars: " ++ show (HMS.size mvsTypes - HMS.size mvsBodies)
        when mvReport $ do
          drawLine
          forM_ (sortBy (comparing fst) $ HMS.toList mvsTypes) $ \(mv, mvType) -> do
            let mbBody = HMS.lookup mv mvsBodies
            when (isNothing mbBody || not mvOnlyUnsolved) $ do
              mvTypeDoc <- prettyTerm sig mvType
              putStrLn $ render $
                PP.pretty mv <+> PP.parens (PP.pretty (mvSrcLoc mv)) <+> ":" //> mvTypeDoc
              when (not mvOnlyUnsolved) $ do
                mvBody <- case HMS.lookup mv mvsBodies of
                  Nothing      -> return "?"
                  Just mvBody0 -> prettyTerm sig mvBody0
                putStrLn $ render $ PP.pretty mv <+> "=" <+> PP.nest 2 mvBody
              putStrLn ""
      noProblemsSummary <- confNoProblemsSummary <$> readConf
      problemsReport <- confProblemsReport <$> readConf
      when (not noProblemsSummary || problemsReport) $  do
        drawLine
        putStrLn . render =<< prettySolveState sig problemsReport (tsState ts ^. csSolveState)
      drawLine

    drawLine =
      putStrLn "------------------------------------------------------------------------"

-- Commands
------------------------------------------------------------------------

data Command
  = TypeOf A.Expr
  | Normalize A.Expr
  | ShowConstraints
  deriving (Eq, Show)

parseCommand :: A.Scope -> String -> Either PP.Doc Command
parseCommand scope s = runReadP $
  (do void $ ReadP.string ":t "
      return (\s' -> TypeOf <$> parseAndScopeCheck s')) <|>
  (do void $ ReadP.string ":n "
      return (\s' -> Normalize <$> parseAndScopeCheck s')) <|>
  (do void $ ReadP.string ":c"
      ReadP.eof
      return (\_ -> Right ShowConstraints))
  where
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
      typeDoc <- prettyTermTC type_
      return $ "type:" //> typeDoc
    Normalize synT -> runTC' $ do
      (t, type_) <- inferExpr Ctx.Empty synT
      typeDoc <- prettyTermTC type_
      tDoc <- prettyTermTC t
      return $
        "type:" //> typeDoc $$
        "term:" //> tDoc
    ShowConstraints -> runTC' $ do
      mapTC csSolveState (prettySolveStateTC True)
  where
    runTC' m = do
      mbErr <- runTC False ts m
      let doc = case mbErr of
                  Left err       -> "Error:" //> err
                  Right (doc0, _) -> doc0
      return (doc, ts)
