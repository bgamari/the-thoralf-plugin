{-# LANGUAGE TypeFamilies       #-}
{-# LANGUAGE TypeInType         #-}
{-# LANGUAGE TypeOperators      #-}
{-# LANGUAGE GADTs              #-}
{-# LANGUAGE StandaloneDeriving #-}


{-# OPTIONS_GHC -Wno-unused-top-binds #-}
{-# OPTIONS_GHC -Wno-orphans #-}


module ThoralfPlugin.Plugin ( plugin, thoralfPlugin ) where

-- Simple imports:
import Prelude hiding ( showList )
import FastString ( fsLit )
import Data.Maybe ( mapMaybe )
import Data.List ( partition, intersperse )
import qualified Data.Map.Strict as M
import qualified Data.Set as Set
import qualified SimpleSMT as SMT
import Control.Monad ( sequence_ )
import Class ( Class(..) )
import System.IO.Error


-- GHC API imports:
import GhcPlugins ( Plugin (..), defaultPlugin, getUnique, getOccName )
import TcPluginM ( tcPluginIO, lookupOrig, tcLookupClass
                 , findImportedModule, FindResult(..), zonkCt )
import TcRnTypes
  ( WantedConstraints, Ct, TcPluginM, TcPluginResult (..)
  , TcPlugin (..), isGivenCt  )
import TcType ( isMetaTyVar )
import TcEvidence ( EvTerm(..) )
import TyCoRep ( UnivCoProvenance(..) )
import Coercion ( mkUnivCo, Role(..)  )
import Type ( Type )
import Var ( Var, isTcTyVar )
import Module ( Module, mkModuleName )
import OccName ( mkTcOcc )
import Outputable ( showSDocUnsafe, ppr )


-- Internal Imports
import ThoralfPlugin.Encode ( thoralfTheories )
import ThoralfPlugin.Convert
import ThoralfPlugin.Encode.TheoryEncoding ( TheoryEncoding (..) )

-- Renaming
type Set = Set.Set
type Map = M.Map


plugin :: Plugin
plugin = defaultPlugin {tcPlugin = const (Just currentPlugin)}

currentPlugin :: TcPlugin
currentPlugin = thoralfPlugin False thoralfTheories


type Debug = Bool

thoralfPlugin :: Debug -> TcPluginM TheoryEncoding -> TcPlugin
thoralfPlugin debug seed = TcPlugin
  { tcPluginInit = mkThoralfInit debug seed
  , tcPluginSolve = thoralfSolver debug  -- Debug flag
  , tcPluginStop = thoralfStop
  }


data ThoralfState where
  ThoralfState ::
    { smtSolver :: SMT.Solver
    , theoryEncoding :: TheoryEncoding
    , disEqClass :: Class
    } -> ThoralfState



mkThoralfInit :: Debug -> TcPluginM TheoryEncoding -> TcPluginM ThoralfState
mkThoralfInit debug seed = do
  encoding <- seed
  let findModule = findImportedModule
  (Found _ disEqModule) <- findModule disEqName (Just pkgName)
  disEq <- findClass disEqModule "DisEquality"
  let decs = startDecs encoding
  z3Solver <- tcPluginIO $ do
    let logLevel = if debug then 0 else 1
    logger <- SMT.newLogger logLevel
    z3Solver <- grabSMTsolver logger
    SMT.ackCommand z3Solver typeDataType
    _ <- traverse (SMT.ackCommand z3Solver) $ map SMT.Atom decs
    SMT.push z3Solver
    return z3Solver
  return $ ThoralfState z3Solver encoding disEq

  where

    disEqName = mkModuleName "ThoralfPlugin.Theory.DisEq"
    pkgName = fsLit "thoralf-plugin"

    findClass :: Module -> String -> TcPluginM Class
    findClass md strNm = do
        name <- lookupOrig md (mkTcOcc strNm)
        tcLookupClass name

    solverOpts = [ "-smt2", "-in" ]

    grabSMTsolver :: SMT.Logger -> IO SMT.Solver
    grabSMTsolver logger = SMT.newSolver "z3" solverOpts (Just logger)

    typeDataType = SMT.Atom typeData
    typeData = "(declare-datatypes () ((Type (apply (fst Type) \
               \ (snd Type)) (lit (getstr String)))))"


thoralfStop :: ThoralfState -> TcPluginM ()
thoralfStop (ThoralfState {smtSolver = solver}) = do
  _ <- tcPluginIO (SMT.stop solver)
  return ()



thoralfSolver :: Debug ->
  ThoralfState -> [Ct] -> [Ct] -> [Ct] -> TcPluginM TcPluginResult
thoralfSolver debug (ThoralfState smt encode deCls) gs ws ds = do
  zonkedCts <- zonkEverything (gs ++ ws ++ ds)
  _ <- printCts debug False gs ws ds
  case convertor deCls encode zonkedCts of
    Nothing -> do
      _ <- printCts debug True gs ws ds
      return $ TcPluginOk [] []
    Just (parsedSExprs, parseDeclrs) -> do
      let partSExpr = partition (isGivenCt . snd) parsedSExprs
      (givenSEqs, wantedSEqs) <- return partSExpr
      case map (\(a,b) -> (SMT.not a,b)) wantedSEqs of
        []                  -> return $ TcPluginOk [] []
        ((wEq, wCt): wSEqs) -> do
          let relevantWC = wCt : (map snd wSEqs)
          let wantedSExpr = foldl SMT.or wEq (map fst wSEqs)
          let givenSExprs = map fst givenSEqs
          printParsedInputs debug givenSExprs wantedSExpr parseDeclrs
          givenCheck <- tcPluginIO $
            flip catchIOError (const $ return SMT.Sat) $ do
              SMT.push smt
              sequence_ $ map (SMT.ackCommand smt) parseDeclrs
              sequence_ $ map (SMT.assert smt) givenSExprs
              SMT.check smt
          case givenCheck of
            SMT.Unknown ->
              (tcPluginIO $ SMT.pop smt) >> (return $ TcPluginOk [] [])
            SMT.Unsat -> do
              tcPluginIO $ (putStrLn "Inconsistent givens.") >> (SMT.pop smt)
              return $ TcPluginContradiction []
            SMT.Sat -> do
              wantedCheck <- tcPluginIO $
                flip catchIOError (const $ return SMT.Sat) $ do
                  SMT.assert smt wantedSExpr
                  SMT.check smt
              case wantedCheck of
                SMT.Unsat ->
                  (tcPluginIO $ SMT.pop smt) >>
                  (return $ TcPluginOk (mapMaybe addEvTerm relevantWC) [])
                SMT.Sat ->
                  (tcPluginIO $ SMT.pop smt) >> (return $ TcPluginOk [] [])
                SMT.Unknown ->
                  (tcPluginIO $ SMT.pop smt) >> (return $ TcPluginOk [] [])



-- * Solver Helper Functions
--------------------------------------------------------------------------------

-- Note: We assume the use of addEvTerm is non-failing.
-- That is, we assume (length $ mapMaybe addEvTerm wCts) == length wCts.

addEvTerm :: Ct -> Maybe (EvTerm, Ct)
addEvTerm ct = do
  (t1,t2,ct') <- maybeExtractTyEq ct
  -- We never have a wanted disequality.
  return (makeEqEvidence "Fm Plugin" (t1,t2), ct')


printParsedInputs :: Bool -> [SExpr] -> SExpr -> [SExpr] -> TcPluginM ()
printParsedInputs True givenSExprs wantedSExpr parseDeclrs = do
  tcPluginIO $ do
    putStrLn $ "Given SExpr: \n" ++
      (show $ map (`SMT.showsSExpr`  "") givenSExprs)
    putStrLn $ "Wanted SExpr: \n" ++
      (SMT.showsSExpr wantedSExpr "")
    putStrLn $ "Variable Decs: \n" ++
      (show $ map (`SMT.showsSExpr`  "") parseDeclrs)
printParsedInputs False _ _ _ = return ()


printCts :: Bool -> Bool -> [Ct] -> [Ct] -> [Ct] -> TcPluginM TcPluginResult
printCts True bool gs ws ds = do
  let iffail = if bool then "Parse Failure" else "Solver Call Start:"
  tcPluginIO $ do
    putStrLn "\n\n  ----- Plugin Call HERE !!! ------\n\n"
    putStrLn iffail
    putStrLn $ "\tGivens: \n" ++ showList gs
    putStrLn $ "\tWanteds: \n" ++ showList ws
    putStrLn $ "\tDesireds: \n" ++ showList ds
  return $ TcPluginOk [] []
printCts False _ _ _ _ = return $ TcPluginOk [] []


zonkEverything :: [Ct] -> TcPluginM [Ct]
zonkEverything [] = return []
zonkEverything (x:xs) = do
  c <- zonkCt x
  cs <- zonkEverything xs
  return (c:cs)



-- make EvTerms for any two types
-- Give the types inside a Predtree of the form (EqPred NomEq t1 t2)
makeEqEvidence :: String -> (Type, Type) -> EvTerm
makeEqEvidence s (t1,t2) =
  EvCoercion $ mkUnivCo (PluginProv s) Nominal t1 t2





-- *  Printing
--------------------------------------------------------------------------------


instance Show Type where
  show = showSDocUnsafe . ppr

instance Show Var where
  show v = nicename ++ ":" ++  classify where

    nicename = varOccName v ++ "_" ++ varUnique v
    classify = classifyVar v

varOccName :: Var -> String
varOccName = showSDocUnsafe . ppr . getOccName

varUnique :: Var -> String
varUnique = show . getUnique

classifyVar :: Var -> String
classifyVar v | isTcTyVar v = case isMetaTyVar v of
                  True ->  "t"
                  False -> "s"
              | otherwise = "irr"



showTupList :: (Show a, Show b) => [(a,b)] -> String
showTupList xs =
  "[\n" ++ concat (intersperse "\n" (map mkEquality xs)) ++ "\n]"
  where
    mkEquality (a,b) = (show a) ++ " ~ " ++ (show b)

showList :: Show a => [a] -> String
showList xs =
  "[\n" ++ concat (intersperse "\n" (map show xs)) ++ "\n]"

instance Show Ct where
  show ct = case maybeExtractTyEq ct of
    Just (t1,t2,_) -> show (t1,t2)
    Nothing -> showSDocUnsafe $ ppr $ ct

instance Show WantedConstraints where
  show = showSDocUnsafe . ppr


