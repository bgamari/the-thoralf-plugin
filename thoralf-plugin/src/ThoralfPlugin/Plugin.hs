{-# LANGUAGE TypeFamilies, TypeInType, TypeOperators,
    GADTs, RecordWildCards, StandaloneDeriving #-}
module ThoralfPlugin.Plugin ( plugin, thoralfPlugin ) where

--------------------------- IMPORTS ----------------------------

-- Simple imports:
import Prelude hiding ( showList )
import FastString ( unpackFS, fsLit )
import Data.Maybe ( mapMaybe, catMaybes )
import Data.List ( partition, intersperse, nub, find )
import System.IO ( IO(..) )
import qualified Data.Kind as Kind
import qualified Data.Map.Strict as M
import qualified Data.Set as Set
import qualified SimpleSMT as SMT
import Control.Monad ( sequence_ )
import Class ( Class(..) )

-- GHC API imports:
import GhcPlugins ( Plugin (..), defaultPlugin, getUnique, getOccName )
import TcPluginM ( tcPluginIO, tcPluginTrace
                 , tcLookupTyCon, lookupOrig, tcLookupClass
                 , findImportedModule, FindResult(..), zonkCt
                 , unsafeTcPluginTcM
                 )
import TcRnTypes( Ct, TcPlugin(..), TcPluginResult (..),
                  ctEvidence, TcPluginM, ctEvPred, CtLoc,
                  mkNonCanonical, ctLoc, isGivenCt, isDerivedCt,
                  isWantedCt, ctPred, WantedConstraints(..),
                  Implication(..)
                )
import TysWiredIn ( maybeTyCon, promotedNothingDataCon, promotedJustDataCon
                  , liftedTypeKind, typeSymbolKind, typeSymbolKindCon
                  )
import TcType ( eqType, isMetaTyVar, Kind, TcType, TcTyVar )
import TcEvidence ( EvTerm(..) )
import TyCoRep ( UnivCoProvenance(..) )
import Coercion ( mkUnivCo, Role(..), mkCoercionType    )
import Type ( Type, classifyPredType, PredTree(..),
              EqRel(..), splitTyConApp_maybe, isStrLitTy,
              splitFunTy_maybe, getTyVar_maybe, tyVarKind,
              tyConAppTyCon_maybe,
              mkStrLitTy, PredType, mkPrimEqPred,
              isTyVar, typeKind, nonDetCmpType, coreView,
              isNumLitTy
            )
import Var ( TyVar, Var, isTcTyVar, varName )
import TyCon ( TyCon(..), tyConKind )
import Module ( Module, mkModuleName )
import OccName ( mkTcOcc )
import Outputable ( SDoc(..), showSDocUnsafe, ppr, pprPrec )

-- Internal Imports
import ThoralfPlugin.Box.TheoryBox
import ThoralfPlugin.Box.Nat ( natSeed )
import ThoralfPlugin.Box.FiniteMap ( fmSeed )
import ThoralfPlugin.Box.UoM ( uomSeed )
import ThoralfPlugin.Box.Symbol ( symbolSeed )


-- Renaming
type Set = Set.Set
type Map = M.Map

--------------------------- END IMPORTS ----------------------------


{-
# RULES FOR USING PLUGIN LIBRARY

(*) Don't make data types with the same name as Type with constructors
`apply` or `lit`

(*) Your theories specify data types for z3 without conflicting each other.
So, we should document somewhere the collection of names.
For example, the FM stuff will need to specify Maybe:
  (declare-datatypes (T) ((Maybe nothing (just (fromJust T)))))

(*) Parenthesis around functions that parse alter:
    "(store (...) (...) (...) )"

(*) The syntactic parts also should only generate FunTy's and TyConApp's.
    Nothing else. No AppTy's

(*) None of the theorybox functions deal with type variables !!!

[Ignore this complication for now -- fake taus pose a problem!!!]
(*) Your encoding with type families doesn't allow for the creation of Tau type
variables, especially fake Tau type variables!


# DESIGN CHOICES I MADE

(*) Note to self: look for some sheet of your note where this is mentioned.
(*) We do solver calls in batches. Either all the wanted constraints follow or
at least one didn't follow.
(*) Ignore plugin-solver calls where we have no wanted constraints.
(*) (Obviously the choice to make an Err plugin with SMT.)
(*) In dealing with types we can't break down with any of our theories
    and are no type variables, we only deal with the case TyConApp and FunTy
    -- not with AppTy !
(*) Using the show of uniques for tyvars to display them.
I'm not sure if this will work with what z3 allows tyvars to be.
(*) Assuming I can either parse all typeEq/DisEq's or something is wrong
This ^ point is important. It prevents the fake tau problem from escaping the
domain I deal with it in. Because of the way GHC breaks things down and traces the
wanted constraint tree, I don't have the fake taus causing issues. The only calls
where smt solving impacts constraints solving are those completely within
my known theories.


# TODO

(*) Test it with examples that we can put in the paper.
(*) Clean imports to only those that are needed.
(*) Documentation!!!

-}



--------------------- TOP LEVEL PLUGIN INTERFACE --------------------
--Recall: type TheorySeed = TcPluginM TheoryBox

plugin :: Plugin
plugin = defaultPlugin {
  tcPlugin = const (Just defaultThoralfPlugin)
  }

thoralfPlugin :: TheorySeed -> TcPlugin
thoralfPlugin seed = TcPlugin
  { tcPluginInit = mkThoralfInit seed
  , tcPluginSolve = thoralfSolver False       -- BOOLEAN for debugging printing
  , tcPluginStop = thoralfStop
  }

defaultThoralfPlugin :: TcPlugin
defaultThoralfPlugin = thoralfPlugin currentDefaultSeed

data ThoralfState where
  ThoralfState ::
    { smtSolver :: SMT.Solver
    , theoryBox :: TheoryBox
    , classForDisEq :: Class
    } -> ThoralfState

--------------------- END TOP LEVEL PLUGIN INTERFACE --------------------




------------------------------ TOP LEVEL FUNCTIONS ----------------------

-- CITE: Looked at Diatski's code.

mkThoralfInit :: TheorySeed -> TcPluginM ThoralfState
mkThoralfInit seed = do
  theorybox <- seed
  (Found location disEqModule) <- findImportedModule disEqModuleName (Just pkgName)
  disEqClass <- findClass disEqModule "DisEquality"
  let decs = startDecs theorybox
  z3SMTsolver <- tcPluginIO $ do
    let logLevel = 1 -- 0 --< for debugging
    logger <- SMT.newLogger logLevel
    z3SMTsolver <- grabSMTsolver logger
    SMT.ackCommand z3SMTsolver typeDataType
    sequence_ $ map (SMT.ackCommand z3SMTsolver) decs
    SMT.push z3SMTsolver
    return z3SMTsolver
  return $
    ThoralfState { smtSolver = z3SMTsolver
                 , theoryBox = theorybox
                 , classForDisEq = disEqClass }
  where
    disEqModuleName = mkModuleName "ThoralfPlugin.Theory.DisEq"
    pkgName = fsLit "thoralf-plugin"
    findClass :: Module -> String -> TcPluginM Class
    findClass mod strName = do
      name <- lookupOrig mod (mkTcOcc strName)
      tcLookupClass name
    solverOpts = [ "-smt2", "-in" ]
    grabSMTsolver :: SMT.Logger -> IO SMT.Solver
    grabSMTsolver logger = SMT.newSolver "z3" solverOpts (Just logger)
    typeDataType =
      SMT.Atom "(declare-datatypes\
               \() ((Type (apply (fst Type) (snd Type))\
               \(lit (getstr String)))))"



thoralfStop :: ThoralfState -> TcPluginM ()
thoralfStop (ThoralfState {smtSolver = solver}) = do
  tcPluginIO (SMT.stop solver)
  return ()

-- NOTE: the ThoralfState pattern match is sensitive to change

thoralfSolver :: Bool -> ThoralfState -> [Ct] -> [Ct] -> [Ct] -> TcPluginM TcPluginResult
thoralfSolver debug (ThoralfState smt box deCls) gs ws ds = do
  zonkedCts <- zonkEverything (gs ++ ws ++ ds)
  printCts debug False gs ws ds
  case parser deCls box zonkedCts of
    Nothing -> do
      printCts debug True gs ws ds
      return $ TcPluginOk [] []
    Just (parsedSExprs, parseDeclrs) -> do
      (givenSEqs, wantedSEqs) <- return (partition (isGivenCt . snd) parsedSExprs)
      case map (\(a,b) -> (SMT.not a,b)) wantedSEqs of
        []                  -> return $ TcPluginOk [] []
        ((wEq, wCt): wSEqs) -> do
          let relevantWC = wCt : (map snd wSEqs)
          let wantedSExpr = foldl SMT.or wEq (map fst wSEqs)
          let givenSExprs = map fst givenSEqs
          printParsedInputs debug givenSExprs wantedSExpr parseDeclrs
          givenCheck <- tcPluginIO $
            (SMT.push smt) >> (sequence_ $ map (SMT.ackCommand smt) parseDeclrs) >>
            (sequence_ $ map (SMT.assert smt) givenSExprs) >> (SMT.check smt)
          case givenCheck of
            SMT.Unsat -> do
              tcPluginIO $ (putStrLn "Inconsistent givens.") >> (SMT.pop smt)
              return $ TcPluginContradiction []
            SMT.Sat -> do
              wantedCheck <- tcPluginIO $ (SMT.assert smt wantedSExpr) >> (SMT.check smt)
              case wantedCheck of
                SMT.Unsat ->
                  (tcPluginIO $ SMT.pop smt) >>
                  (return $ TcPluginOk (mapMaybe addEvTerm relevantWC) [])
                SMT.Sat -> (tcPluginIO $ SMT.pop smt) >> (return $ TcPluginOk [] [])


-- Note: We assume the use of addEvTerm is non-failing.
-- That is, we assume (lenght $ mapMaybe addEvTerm wCts) == length wCts.

addEvTerm :: Ct -> Maybe (EvTerm, Ct)
addEvTerm ct = do
  (t1,t2,ct) <- maybeExtractTyEq ct      -- never have a wanted disEquality
  return (makeEqEvidence "Fm Plugin" (t1,t2), ct)


printParsedInputs True givenSExprs wantedSExpr parseDeclrs = do
  tcPluginIO $ do
    putStrLn ("Given SExpr: \n" ++ (show $ map (`SMT.showsSExpr`  "") givenSExprs))
    putStrLn ("Wanted SExpr: \n" ++ (SMT.showsSExpr wantedSExpr ""))
    putStrLn ("Variable Decs: \n" ++ (show $ map (`SMT.showsSExpr`  "") parseDeclrs))
printParsedInputs False givenSExprs wantedSExpr parseDeclrs = return ()


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
printCts False bool gs ws ds = return $ TcPluginOk [] []

zonkEverything :: [Ct] -> TcPluginM [Ct]
zonkEverything [] = return []
zonkEverything (x:xs) = do
  c <- zonkCt x
  cs <- zonkEverything xs
  return (c:cs)

-------------------------- END TOP LEVEL FUNCTIONS ----------------------

{-
# Paradigm For Implementation
You just make TheorySeed's and add them together.
(I didn't bother with a monoid instance.)
-}


currentDefaultSeed :: TheorySeed
currentDefaultSeed =
  sumSeeds [ natSeed
           , fmSeed
           , symbolSeed
           , uomSeed
           ]



----------------------------------------------------------
----------------------------------------------------------
----------------------------------------------------------
--                    SMT WORK                          --
----------------------------------------------------------
----------------------------------------------------------

type TypePair = (Type,Type,Ct)

-- Returns ([Converted TypeEq/DisEqs], [Declarations])
parser :: Class -> TheoryBox -> [Ct] -> Maybe ([(SExpr, Ct)], [SExpr])
parser cls box cts = do
  let tyDisEqs = extractDisEq cls cts
  let tyEqs = extractEq cts
  (sDisEqs, tyvar1, kvars1, df1) <- innerParser box tyDisEqs
  (sEqs, tyvar2, kvars2, df2) <- innerParser box tyEqs
  let defaultTyVarConst = umap mkDefConst $ df1 ++ df2
  makingTvConst <-
    monadMap (mkTyVarConst box) $ Set.toList $ Set.fromList (tyvar1 ++ tyvar2)
  let tyVarConst = map fst makingTvConst
  let moreKindVar = concat $ map snd makingTvConst
  let sortConst = umap mkSort (kvars1 ++ kvars2 ++ moreKindVar)
  let decs = sortConst ++ defaultTyVarConst ++ tyVarConst -- sorts first!
  let equalSExprs = map mkEqExpr sEqs
  let disEqualSExprs = map mkDisEqExpr sDisEqs
  return (equalSExprs ++ disEqualSExprs, decs)

umap :: Ord a => (a -> b) -> [a] -> [b]
umap f xs = map f $ Set.toList $ Set.fromList xs

mkEqExpr :: (SExpr, SExpr, Ct) -> (SExpr, Ct)
mkEqExpr (s1,s2,ct) = (SMT.eq s1 s2, ct)

mkDisEqExpr :: (SExpr, SExpr, Ct) -> (SExpr, Ct)
mkDisEqExpr (s1,s2,ct) = ((SMT.not $ SMT.eq s1 s2), ct)

type TypeVars = [TyVar]
type KindVars = [TyVar]
type DefVars = [TyVar] -- for defaulting: (declare-const lk3w Type)
type ParseResult = ([(SExpr, SExpr, Ct)], TypeVars, KindVars, DefVars)


-- we insist all type equalities to parse
-- this might be a terrible idea
innerParser :: TheoryBox -> [TypePair] -> Maybe ParseResult
innerParser box [] = Just ([],[],[],[])
innerParser box (e:es) = do
  (e', tvars1, kvars1, dvars1) <- tyPairConvertor box e
  (es', tvars2, kvars2, dvars2) <- innerParser box es
  return (e':es', tvars1 ++ tvars2, kvars2 ++ kvars2, dvars1 ++ dvars2)

type OneConvert = ((SExpr, SExpr, Ct), TypeVars, KindVars, DefVars)
tyPairConvertor :: TheoryBox -> TypePair -> Maybe OneConvert
tyPairConvertor box (t1,t2,ct) = do
  (t1Sexp, tvars1, kvars1, df1) <- tyConvertor box t1
  (t2Sexp, tvars2, kvars2, df2) <- tyConvertor box t2
  return
    ((t1Sexp, t2Sexp, ct), tvars1 ++ tvars2, kvars1 ++ kvars2, df1 ++ df2)


----------------------------------------------------------
-- Making Declarations
----------------------------------------------------------

mkDefConst :: TyVar -> SExpr
mkDefConst tv = let
  name = show $ getUnique tv
  smtStr = "(declare-const " ++ name ++ " Type)"
  in SMT.Atom smtStr

mkSort :: TyVar -> SExpr
mkSort tv = let
  name = "Sort" ++ (show $ getUnique tv)
  smtStr = "(declare-sort " ++ name ++ ")"
  in SMT.Atom smtStr

mkTyVarConst :: TheoryBox -> TyVar -> Maybe (SExpr, KindVars)
mkTyVarConst box tv = do
  tvKindConv <- kindConvertor box (tyVarKind tv)
  let kindStr = fst tvKindConv
  let kindVars = snd tvKindConv
  let name = show $ getUnique tv
  let smtStr = "(declare-const " ++ name ++ " " ++ kindStr ++ ")"
  return (SMT.Atom smtStr, kindVars)


monadMap :: Monad m => (a -> m b) -> [a] -> m [b]
monadMap f [] = return []
monadMap f (x:xs) = do
  b <- f x
  bs <- monadMap f xs
  return (b:bs)

----------------------------------------------------------
-- END: Making Declarations
----------------------------------------------------------




----------------------------------------------------------
-- Extraction
----------------------------------------------------------

extractEq :: [Ct] -> [TypePair]
extractEq = mapMaybe maybeExtractTyEq

maybeExtractTyEq :: Ct -> Maybe TypePair
maybeExtractTyEq ct = case classifyPredType $ ctPred ct of
  EqPred NomEq t1 t2 -> Just (simpIfCan t1, simpIfCan t2, ct)
  _ -> Nothing
  where
    simpIfCan :: Type -> Type
    simpIfCan t = case coreView t of
      Just t' -> t'
      Nothing -> t


extractDisEq :: Class -> [Ct] -> [TypePair]
extractDisEq cls = mapMaybe (maybeExtractTyDisEq cls)

maybeExtractTyDisEq :: Class -> Ct -> Maybe TypePair
maybeExtractTyDisEq disEqCls ct = case classifyPredType $ ctPred ct of
  ClassPred cls (k: t1 : t2 : xs) ->
    case cls == disEqCls of
      True -> Just (t1,t2,ct)
      False -> Nothing
  _ -> Nothing


{-- Ord and Eq instances for Type
instance Eq Type where
  (==) = eqType

instance Ord Type where
  compare = nonDetCmpType
-}

----------------------------------------------------------
-- END Extraction
----------------------------------------------------------





----------------------------------------------------------
-- Type -> SExpr Conversion
----------------------------------------------------------


-- Recall: Type/KindVars = [TyVar]

tyConvertor :: TheoryBox -> Type -> Maybe (SExpr, TypeVars, KindVars, DefVars)
tyConvertor box ty = do
  (strExp, tvars, kvars, defvars) <- innerTyConv box ty
  return (SMT.Atom strExp, tvars, kvars, defvars)

innerTyConv :: TheoryBox -> Type -> Maybe (String, TypeVars, KindVars, DefVars)
innerTyConv box ty = case tryTyVarConvert ty of
  Just (varNm, var) -> Just (varNm, [var], [], [])
  Nothing -> tryTyTheories box ty

-- (1)
tryTyVarConvert :: Type -> Maybe (String, TyVar)
tryTyVarConvert ty = do
  tyvar <- getTyVar_maybe ty
  () <- assertIsSkolem tyvar
  let tvarName = show $ getUnique tyvar
  return (tvarName, tyvar)
  where
    assertIsSkolem :: TyVar -> Maybe ()
    assertIsSkolem tyvar = case isSkolemVar tyvar of
      True -> Just ()
      False -> Nothing

-- (2)
tryTyTheories :: TheoryBox -> Type -> Maybe (String, TypeVars, KindVars, DefVars)
tryTyTheories box@(TheoryBox {typeConvs = tconvs}) ty =
  case tryThese tconvs ty of
    Just (TyKit (types, kinds, strMaker)) -> do
      recurTypes <- vecMapAll (innerTyConv box) types
      recurKinds <- vecMapAll (kindConvertor box) kinds
      let filledTyHoles = vecMap (\(a,b,c,d) -> a) recurTypes
      let filledKdHoles = vecMap fst recurKinds
      let mkList = concat . vecMapList id
      let tyHoleTyVars = mkList $ vecMap (\(a,b,c,d) -> b) recurTypes
      let tyHoleKVars = mkList $ vecMap (\(a,b,c,d) -> c) recurTypes
      let defVars = mkList $ vecMap (\(a,b,c,d) -> d) recurTypes
      let kHoleKVars = mkList $ vecMap snd recurKinds
      let kVars = tyHoleKVars ++ kHoleKVars
      let convertedType = strMaker filledTyHoles filledKdHoles
      return (convertedType, tyHoleTyVars, kVars, defVars)
    Nothing -> defaultTyConv box ty


tryThese :: [a -> Maybe b] -> a -> Maybe b
tryThese [] _ = Nothing
tryThese (f:fs) a = case f a of
  Nothing -> tryThese fs a
  Just b -> Just b



-- (3) [Recall, we are assuming the equational theory of Type is now syntatic.]
defaultTyConv :: TheoryBox -> Type -> Maybe (String, TypeVars, KindVars, DefVars)
defaultTyConv box ty =
  case getTyVar_maybe ty of
    -- we redo type var checking b/c
    -- trivialFun & trivialTyCon recursivly call this fn
    Just tyvar -> let strTy = show $ getUnique tyvar
      in Just (strTy, [], [], [tyvar])
    Nothing -> defaultFunTyConvert box ty


defaultFunTyConvert :: TheoryBox -> Type -> Maybe (String, TypeVars, KindVars, DefVars)
defaultFunTyConvert box ty = case splitFunTy_maybe ty of
  Nothing -> defaultTyConConv box ty
  Just (tyIn, tyOut) -> do
    (strIn, tvs1, kvs1, df1) <- defaultTyConv box tyIn
    (strOut, tvs2, kvs2, df2) <- defaultTyConv box tyIn
    let smtStr = "(apply (apply (lit \"->\") " ++ strIn ++ ") " ++ strOut ++ ")"
    return (smtStr, tvs1 ++ tvs2, kvs1 ++ kvs2, df1 ++ df2)


defaultTyConConv :: TheoryBox -> Type -> Maybe (String, TypeVars, KindVars, DefVars)
defaultTyConConv box ty = do
  (tcon, types) <- splitTyConApp_maybe ty
  case types of
    [] -> let smtStr = "(lit \"" ++ (show $ getUnique tcon) ++ "\")"
      in Just (smtStr, [], [], [])
    tys@(_:_) -> do
      let tconString = "(lit \"" ++ (show $ getUnique tcon) ++ "\")"
      (strConvTypes, tv, kv, dv) <- maybeGetDefaultConvs box types
      let smtString = foldl makeSExprApp tconString strConvTypes
      return (smtString, tv, kv, dv)

maybeGetDefaultConvs :: TheoryBox -> [Type] -> Maybe ([String], TypeVars, KindVars, DefVars)
maybeGetDefaultConvs box [] = Just ([],[],[],[])
maybeGetDefaultConvs box (x:xs) = do
  (strConv, tvars, kvars, defvars) <- defaultTyConv box x
  (strConvs, tvars', kvars', defvars') <- maybeGetDefaultConvs box xs
  let tv = tvars ++ tvars'
  let kv = kvars ++ kvars'
  let dv = defvars ++ defvars'
  return (strConv:strConvs, tv, kv, dv)


makeSExprApp :: String -> String -> String
makeSExprApp func arg = "(apply " ++ func ++ " " ++ arg ++ ")"




{-
-- (4) [Recall, we are assuming the equational theory of Type, is now syntatic.]
trivialConvert :: TheoryBox -> Type -> Maybe (SExpr, [TyVar])
trivialConvert box ty =
  case tryTyVarConvert ty of
    -- we redo type var checking b/c
    -- trivialFun & trivialTyCon recursivly call this fn
    Just (sexpr, tyvar) -> Just (sexpr, [tyvar])
    Nothing -> trivialFunTyConvert box ty



trivialFunTyConvert :: TheoryBox -> Type -> Maybe (SExpr, [TyVar])
trivialFunTyConvert box ty = case splitFunTy_maybe ty of
  Nothing -> trivialTyConConvert box ty
  Just (tyIn, tyOut) -> do
    (SMT.Atom strIn, tvs1) <- trivialConvert box tyIn
    (SMT.Atom strOut, tvs2) <- trivialConvert box tyIn
    let smtStr = "(apply (apply (lit \"->\") " ++ strIn ++ ") " ++ strOut ++ ")"
    return (SMT.Atom smtStr, tvs1 ++ tvs2)


trivialTyConConvert :: TheoryBox -> Type -> Maybe (SExpr, [TyVar])
trivialTyConConvert box ty = do
  (tcon, types) <- splitTyConApp_maybe ty
  case types of
    [] -> let
      smtStr = "(lit \"" ++ (show $ getUnique tcon) ++ "\")"
      in Just (SMT.Atom smtStr, [])
    tys@(_:_) -> do
      let tconString = "(lit \"" ++ (show $ getUnique tcon) ++ "\")"
      (strConvTypes, tyVars) <- maybeGetTrivialConvs box types
      let smtString = foldl makeSExprApp tconString strConvTypes
      return (SMT.Atom smtString, tyVars)


maybeGetTrivialConvs :: TheoryBox -> [Type] -> Maybe ([String], [TyVar])
maybeGetTrivialConvs box [] = Just ([],[])
maybeGetTrivialConvs box (x:xs) = do
  (SMT.Atom string, tyvars) <- trivialConvert box x
  (otherConverts, otherTyvars) <- maybeGetTrivialConvs box xs
  return (string:otherConverts, tyvars ++ otherTyvars)


makeSExprApp :: String -> String -> String
makeSExprApp func arg = "(apply " ++ func ++ " " ++ arg ++ ")"

-}


kindConvertor :: TheoryBox -> Kind -> Maybe (String, KindVars)
kindConvertor box kind = case getTyVar_maybe kind of
  Just tvar -> let name = "Sort" ++ (show $ getUnique tvar)
    in Just (name, [tvar])
  Nothing -> tryKTheories box kind

tryKTheories :: TheoryBox -> Kind -> Maybe (String, KindVars)
tryKTheories box@(TheoryBox {kindConvs = kconvs}) kind =
  case tryThese kconvs kind of
    Nothing -> Just ("Type", []) -- kind defaulting
    Just (KdKit (kholes, strMaker)) -> do
      recur <- vecMapAll (kindConvertor box) kholes
      let filledHoles = vecMap fst recur
      let recurKVars = concat $ vecMapList id $ vecMap snd recur
      let convertedKind = strMaker filledHoles
      return (convertedKind, recurKVars)


vecMapAll :: (a -> Maybe b) -> Vec n a -> Maybe (Vec n b)
vecMapAll f VNil = Just VNil
vecMapAll f (x :> xs) = do
  b <- f x
  bs <- vecMapAll f xs
  return (b :> bs)

vecMapList :: (a -> b) -> Vec n a -> [b]
vecMapList f VNil = []
vecMapList f (x :> xs) = (f x) : (vecMapList f xs)

vecMap :: (a -> b) -> Vec n a -> Vec n b
vecMap f VNil = VNil
vecMap f (x :> xs) = (f x) :> (vecMap f xs)


----------------------------------------------------------
-- END: Type -> SExpr Conversion
----------------------------------------------------------




--   Declaring constants for Type Variables



{-


-- The use of Maybe in these functions is unneccesary, but eases notation.
declareVarSet :: TheoryBox -> Set TyVar -> Maybe [SExpr]
declareVarSet box tyvarSet = declareVarList box (Set.toList tyvarSet)

declareVarList  :: TheoryBox -> [TyVar] -> Maybe [SExpr]
declareVarList _ [] = return []
declareVarList box (t:ts) = do
  e <- declareVar box t
  es <- declareVarList box ts
  return (e:es)

-- e.g., (declare-const m (Array Int (Maybe Type))
declareVar :: TheoryBox -> TyVar -> Maybe SExpr
declareVar box tyvar = do
  let tvKind = tyVarKind tyvar
  kindSExpr <- determineKind box tvKind
  let kindStr = sExprToStr kindSExpr
  let smtStr = "(declare-const " ++ (show $ getUnique tyvar) ++ " " ++ kindStr ++ ")"
  return $ SMT.Atom smtStr


sExprToStr :: SExpr -> String
sExprToStr exp = SMT.showsSExpr exp ""


determineKind ::  TheoryBox -> Kind -> Maybe SExpr
determineKind box kind = case tryThese skindConvs kind of
  Just kindSExpr -> Just kindSExpr
  Nothing -> case tryThese pkindConvs kind of
    Just (ParamRes (holes, mkSExpr)) -> do
      filledHoles <- vecMapMaybe (determineKind box) holes
      return $ mkSExpr filledHoles
    Nothing -> return $ SMT.Atom "Type"          -- default
  where
    skindConvs = simpleConversions box
    pkindConvs = paramConversions box


-- Recall: type Kind = Type




-}

----------------------------------------------------------
----------------------------------------------------------
----------------------------------------------------------
--                   END SMT WORK                       --
----------------------------------------------------------
----------------------------------------------------------










------------------- Printing --------------------------------------------

instance Show Type where
  show = showSDocUnsafe . ppr

instance Show Var where
  show v =
    let
      nicename = varOccName v ++ "_" ++ varUnique v
      -- nicename = varUnique v
      classify = classifyVar v
    in
      nicename ++ ":" ++  classify


varOccName :: Var -> String
varOccName = showSDocUnsafe . ppr . getOccName

varUnique :: Var -> String
varUnique = show . getUnique

classifyVar :: Var -> String
classifyVar v | isTcTyVar v = case isMetaTyVar v of
                  True -> "t"
                  False -> "s"
              | otherwise = "irr"

data VarCat = Tau | Skol | Irr
  deriving Eq

categorizeVar :: Var -> VarCat
categorizeVar var =
  if isTcTyVar var
  then
    if isMetaTyVar var
    then Tau
    else Skol
  else Irr

isSkolemVar :: Var -> Bool
isSkolemVar v = True -- categorizeVar v == Skol

isTauVar :: TyVar -> Bool
isTauVar v = categorizeVar v == Tau

data FmCat = SkolemSpace | TauSpace
deriving instance Eq FmCat
deriving instance Show FmCat


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
------------------- END: Printing ---------------------------------------



-------------------- Library Functions ------------------

-- make EvTerms for any two types
-- Give the types inside a Predtree of the form (EqPred NomEq t1 t2)
makeEqEvidence :: String -> (Type, Type) -> EvTerm
makeEqEvidence s (t1,t2) =
  EvCoercion $ mkUnivCo (PluginProv s) Nominal t1 t2

-------------------- END Library Functions ------------------
