{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
-- TODO add options that are present in TypeCheck
module TypeCheck3
  ( availableTermTypes
  , checkProgram
  , TCState'
  ) where

import           Prelude                          hiding (abs, pi)

import qualified Control.Lens                     as L
import           Control.Monad.Trans.Except       (ExceptT(ExceptT), runExceptT)
import           Data.Proxy                       (Proxy(Proxy))

import           Conf
import           Prelude.Extended
import qualified Syntax.Internal                  as A
import           Term
import           Term.Impl
import           PrettyPrint                      ((<+>), render)
import qualified PrettyPrint                      as PP
import           TypeCheck3.Monad
import           TypeCheck3.Check

-- Type checking
------------------------------------------------------------------------

-- Checking programs
--------------------

availableTermTypes :: [String]
availableTermTypes = ["GR", "S", "H", "SUSP"]

type TCState' t = TCState t (CheckState t)

checkProgram
  :: [A.Decl]
  -> (forall t. (IsTerm t) => TCState' t -> IO a)
  -> IO (Either PP.Doc a)
checkProgram decls ret = do
  tt <- confTermType <$> readConf
  case tt of
    "S"  -> checkProgram' (Proxy :: Proxy Simple)      decls ret
    "GR" -> checkProgram' (Proxy :: Proxy GraphReduce) decls ret
    -- "EW" -> checkProgram' (Proxy :: Proxy EasyWeaken)  conf decls ret
    "H"  -> checkProgram' (Proxy :: Proxy Hashed)      decls ret
    -- "SUSP" -> checkProgram' (Proxy :: Proxy Suspension) conf decls ret
    type_ -> return $ Left $ "Invalid term type" <+> PP.text type_

checkProgram'
    :: forall t a. (IsTerm t)
    => Proxy t -> [A.Decl]
    -> (TCState' t -> IO a)
    -> IO (Either PP.Doc a)
checkProgram' _ decls0 ret = do
    quiet <- confQuiet <$> readConf
    unless quiet $ do
      drawLine
      putStrLn "-- Checking declarations"
      drawLine
    let s = initCheckState
    errOrTs <- runExceptT (goDecls (initTCState s) decls0)
    case errOrTs of
      Left err -> return $ Left err
      Right t  -> Right <$> ret t
  where
    goDecls :: TCState' t -> [A.Decl] -> ExceptT PP.Doc IO (TCState' t)
    goDecls ts [] = do
      -- lift $ unless (tccQuiet conf) $ report ts
      -- TODO report
      return ts
    goDecls ts (decl : decls) = do
      quiet <- confQuiet <$> lift readConf
      debug <- confDebug <$> lift readConf
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
      let debug' = if (not quiet && debug) then enableDebug else id
      ((), ts') <- ExceptT $ runTC ts $ debug' $ checkDecl decl
      goDecls ts' decls

    -- report :: TCState' t -> IO ()
    -- report ts = do
    --   let tr  = tcReport ts
    --   let sig = trSignature tr
    --   when (not (tccNoMetaVarsSummary conf) || tccMetaVarsReport conf) $ do
    --     let mvsTypes  = Sig.metaVarsTypes sig
    --     let mvsBodies = Sig.metaVarsBodies sig
    --     drawLine
    --     putStrLn $ "-- Solved MetaVars: " ++ show (HMS.size mvsBodies)
    --     putStrLn $ "-- Unsolved MetaVars: " ++ show (HMS.size mvsTypes - HMS.size mvsBodies)
    --     when (tccMetaVarsReport conf) $ do
    --       drawLine
    --       forM_ (sortBy (comparing fst) $ HMS.toList mvsTypes) $ \(mv, mvType) -> do
    --         let mbBody = HMS.lookup mv mvsBodies
    --         when (isNothing mbBody || not (tccMetaVarsOnlyUnsolved conf)) $ do
    --           mvTypeDoc <- prettyTerm sig mvType
    --           putStrLn $ render $
    --             PP.pretty mv <+> PP.parens (PP.pretty (A.mvSrcLoc mv)) <+> ":" //> mvTypeDoc
    --           when (not (tccMetaVarsOnlyUnsolved conf)) $ do
    --             mvBody <- case HMS.lookup mv mvsBodies of
    --               Nothing      -> return "?"
    --               Just mvBody0 -> prettyTerm sig mvBody0
    --             putStrLn $ render $ PP.pretty mv <+> "=" <+> PP.nest 2 mvBody
    --           putStrLn ""
    --   when (not (tccNoProblemsSummary conf) || tccProblemsReport conf) $ do
    --     drawLine
    --     putStrLn $ "-- Solved problems: " ++ show (HS.size (trSolvedProblems tr))
    --     putStrLn $ "-- Unsolved problems: " ++ show (Map.size (trUnsolvedProblems tr))
    --     when (tccProblemsReport conf) $ do
    --       drawLine
    --       -- We want to display problems bound to metavars first (the
    --       -- "roots").
    --       let compareStates ps1 ps2 = case (ps1, ps2) of
    --             (WaitingOn (WOAnyMeta _), WaitingOn (WOAnyMeta _)) -> EQ
    --             (WaitingOn (WOAnyMeta _), _)                       -> LT
    --             (_, WaitingOn (WOAnyMeta _))                       -> GT
    --             (_, _)                                             -> EQ
    --       let problems =
    --             sortBy (compareStates `on` problemState . snd) $ Map.toList $ trUnsolvedProblems tr
    --       forM_ problems $ \(pid, (Problem mbProb probState _ _)) -> do
    --         probDoc <- case mbProb of
    --           Nothing   -> return "Waiting to return."
    --           Just prob -> prettyTypeCheckProblem sig prob
    --         putStrLn $ render $
    --           PP.pretty pid $$
    --           PP.indent 2 (PP.pretty probState) $$
    --           PP.indent 2 probDoc
    --         putStrLn ""
    --   drawLine

    drawLine =
      putStrLn "------------------------------------------------------------------------"
