{-# LANGUAGE OverloadedStrings #-}
-- TODO add options that are present in TypeCheck
module TypeCheck2
  ( TypeCheckConf(..)
  , defaultTypeCheckConf
  , availableTermTypes
  , checkProgram
  , TCState'
  , TCReport'
  ) where

import           Prelude                          hiding (abs, pi)

import           Control.Monad.Trans.Except       (ExceptT(ExceptT), runExceptT)
import           Control.Monad.Trans.Maybe        (MaybeT(MaybeT), runMaybeT)
import qualified Data.HashMap.Strict              as HMS
import qualified Data.HashSet                     as HS
import qualified Data.Map.Strict                  as Map
import           Data.Proxy                       (Proxy(Proxy))
import qualified Data.Set                         as Set

import           Prelude.Extended
import           Syntax.Internal                  (Name, MetaVar)
import qualified Syntax.Internal                  as A
import           Term
import           Term.Context                     (Ctx)
import qualified Term.Context                     as Ctx
import           Term.Impl
import qualified Term.Signature                   as Sig
import qualified Term.Telescope                   as Tel
import           PrettyPrint                      (($$), (<+>), (//>), render)
import qualified PrettyPrint                      as PP
import           TypeCheck2.Monad
import           TypeCheck2.Common
import           TypeCheck2.Elaborate             as Elaborate

-- Configuration
------------------------------------------------------------------------

data TypeCheckConf = TypeCheckConf
  { tccTermType                :: String
  , tccQuiet                   :: Bool
  , tccNoMetaVarsSummary       :: Bool
  , tccMetaVarsReport          :: Bool
  , tccMetaVarsOnlyUnsolved    :: Bool
  , tccNoProblemsSummary       :: Bool
  , tccProblemsReport          :: Bool
  , tccDebug                   :: Bool
  , tccCheckMetaVarConsistency :: Bool
  , tccFastGetAbsName          :: Bool
  , tccDisableSynEquality      :: Bool
  }

defaultTypeCheckConf :: TypeCheckConf
defaultTypeCheckConf = TypeCheckConf "GR" True False False False False False False False False False

-- Type checking
------------------------------------------------------------------------

-- Checking programs
--------------------

availableTermTypes :: [String]
availableTermTypes = ["GR", "S", "H", "SUSP"]

checkProgram
  :: TypeCheckConf -> [A.Decl]
  -> (forall t. (IsTerm t) => TCState' t -> IO a)
  -> IO (Either PP.Doc a)
checkProgram conf decls ret =
  case tccTermType conf of
    "S"  -> checkProgram' (Proxy :: Proxy Simple)      conf decls ret
    "GR" -> checkProgram' (Proxy :: Proxy GraphReduce) conf decls ret
    -- "EW" -> checkProgram' (Proxy :: Proxy EasyWeaken)  conf decls ret
    "H"  -> checkProgram' (Proxy :: Proxy Hashed)      conf decls ret
    -- "SUSP" -> checkProgram' (Proxy :: Proxy Suspension) conf decls ret
    type_ -> return $ Left $ "Invalid term type" <+> PP.text type_

checkProgram'
    :: forall t a. (IsTerm t)
    => Proxy t -> TypeCheckConf -> [A.Decl]
    -> (TCState' t -> IO a)
    -> IO (Either PP.Doc a)
checkProgram' _ conf decls0 ret = do
    unless (tccQuiet conf) $ do
      drawLine
      putStrLn "-- Checking declarations"
      drawLine
    let s = TypeCheckState (tccCheckMetaVarConsistency conf)
                           (tccFastGetAbsName conf)
                           (tccDisableSynEquality conf)
    errOrTs <- runExceptT (goDecls (initTCState s) decls0)
    case errOrTs of
      Left err -> return $ Left err
      Right t  -> Right <$> ret t
  where
    goDecls :: TCState' t -> [A.Decl] -> ExceptT PP.Doc IO (TCState' t)
    goDecls ts [] = do
      lift $ unless (tccQuiet conf) $ report ts
      return ts
    goDecls ts (decl : decls) = do
      lift $ unless (tccQuiet conf) $ do
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
      let debug' = if (not (tccQuiet conf) && tccDebug conf) then enableDebug else id
      let describeProblem p =
            withSignatureTermM $ \sig -> prettyTypeCheckProblem sig p
      ((), ts') <- ExceptT $ runTC typeCheckProblem describeProblem ts $ debug' $
        checkDecl decl >> solveProblems_
      goDecls ts' decls

    report :: TCState' t -> IO ()
    report ts = do
      let tr  = tcReport ts
      let sig = trSignature tr
      when (not (tccNoMetaVarsSummary conf) || tccMetaVarsReport conf) $ do
        let mvsTypes  = Sig.metaVarsTypes sig
        let mvsBodies = Sig.metaVarsBodies sig
        drawLine
        putStrLn $ "-- Solved MetaVars: " ++ show (HMS.size mvsBodies)
        putStrLn $ "-- Unsolved MetaVars: " ++ show (HMS.size mvsTypes - HMS.size mvsBodies)
        when (tccMetaVarsReport conf) $ do
          drawLine
          forM_ (sortBy (comparing fst) $ HMS.toList mvsTypes) $ \(mv, mvType) -> do
            let mbBody = HMS.lookup mv mvsBodies
            when (isNothing mbBody || not (tccMetaVarsOnlyUnsolved conf)) $ do
              mvTypeDoc <- prettyTerm sig mvType
              putStrLn $ render $
                PP.pretty mv <+> PP.parens (PP.pretty (A.mvSrcLoc mv)) <+> ":" //> mvTypeDoc
              when (not (tccMetaVarsOnlyUnsolved conf)) $ do
                mvBody <- case HMS.lookup mv mvsBodies of
                  Nothing      -> return "?"
                  Just mvBody0 -> prettyTerm sig mvBody0
                putStrLn $ render $ PP.pretty mv <+> "=" <+> PP.nest 2 mvBody
              putStrLn ""
      when (not (tccNoProblemsSummary conf) || tccProblemsReport conf) $ do
        drawLine
        putStrLn $ "-- Solved problems: " ++ show (HS.size (trSolvedProblems tr))
        putStrLn $ "-- Unsolved problems: " ++ show (Map.size (trUnsolvedProblems tr))
        when (tccProblemsReport conf) $ do
          drawLine
          -- We want to display problems bound to metavars first (the
          -- "roots").
          let compareStates ps1 ps2 = case (ps1, ps2) of
                (WaitingOn (WOAnyMeta _), WaitingOn (WOAnyMeta _)) -> EQ
                (WaitingOn (WOAnyMeta _), _)                       -> LT
                (_, WaitingOn (WOAnyMeta _))                       -> GT
                (_, _)                                             -> EQ
          let problems =
                sortBy (compareStates `on` problemState . snd) $ Map.toList $ trUnsolvedProblems tr
          forM_ problems $ \(pid, (Problem mbProb probState _ _)) -> do
            probDoc <- case mbProb of
              Nothing   -> return "Waiting to return."
              Just prob -> prettyTypeCheckProblem sig prob
            putStrLn $ render $
              PP.pretty pid $$
              PP.indent 2 (PP.pretty probState) $$
              PP.indent 2 probDoc
            putStrLn ""
      drawLine

    drawLine =
      putStrLn "------------------------------------------------------------------------"
