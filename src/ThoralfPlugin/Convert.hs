{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}

module ThoralfPlugin.Convert where

import Data.Maybe ( mapMaybe )
import qualified Data.Set as Set
import qualified SimpleSMT as SMT
import Class ( Class(..) )


-- GHC API imports:
import GhcPlugins ( getUnique )
import TcRnTypes ( Ct, ctPred )
import TcType ( Kind )
import Var ( TyVar )
import Type ( Type, PredTree (..), EqRel (..), getTyVar_maybe
            , splitTyConApp_maybe, splitFunTy_maybe
            , classifyPredType, coreView, tyVarKind )


-- Internal imports
import ThoralfPlugin.Encode.TheoryEncoding
import Data.Vec


-- Renaming
type Set = Set.Set
type SExpr = SMT.SExpr


type TypePair = (Type,Type,Ct)

-- TODO: with new addition, check that the declarations are unique.

-- Returns ([Converted TypeEq/DisEqs], [Declarations])
convertor :: Class -> TheoryEncoding -> [Ct] -> Maybe ([(SExpr, Ct)], [SExpr])
convertor cls encode cts = do
  let tyDisEqs = extractDisEq cls cts
  let tyEqs = extractEq cts
  (sDisEqs, tyvar1, kvars1, df1) <- innerConvertor encode tyDisEqs
  (sEqs, tyvar2, kvars2, df2) <- innerConvertor encode tyEqs
  let defaultTyVarConst = umap mkDefConst $ df1 ++ df2
  let tyvarSet = Set.toList . Set.fromList $ tyvar1 ++ tyvar2
  makingTvConst <- traverse (mkTyVarConst encode) tyvarSet
  let tyVarConst = map fst makingTvConst
  let moreKindVar = concat $ map snd makingTvConst
  let sortConst = umap mkSort (kvars1 ++ kvars2 ++ moreKindVar)
  -- Sorts must come first in list of decs:
  let decs = sortConst ++ defaultTyVarConst ++ tyVarConst
  let equalSExprs = map mkEqExpr sEqs
  let disEqualSExprs = map mkDisEqExpr sDisEqs
  return (equalSExprs ++ disEqualSExprs, decs)


umap :: Ord a => (a -> b) -> [a] -> [b]
umap f = map f . Set.toList . Set.fromList

mkEqExpr :: (SExpr, SExpr, Ct) -> (SExpr, Ct)
mkEqExpr (s1,s2,ct) = (SMT.eq s1 s2, ct)

mkDisEqExpr :: (SExpr, SExpr, Ct) -> (SExpr, Ct)
mkDisEqExpr (s1,s2,ct) = ((SMT.not $ SMT.eq s1 s2), ct)













type TypeVars = [TyVar]
type KindVars = [TyVar]
type DefVars = [TyVar] -- for defaulting: (declare-const lk3w Type)
type ParseResult = ([(SExpr, SExpr, Ct)], TypeVars, KindVars, DefVars)


-- We require that all type equalities parse.
innerConvertor :: TheoryEncoding -> [TypePair] -> Maybe ParseResult
innerConvertor _ [] = Just ([],[],[],[])
innerConvertor encode (e:es) = do
  (e', tvars1, _, dvars1) <- tyPairConvertor encode e
  (es', tvars2, kvars2, dvars2) <- innerConvertor encode es
  return (e':es', tvars1 ++ tvars2, kvars2 ++ kvars2, dvars1 ++ dvars2)

type OneConvert = ((SExpr, SExpr, Ct), TypeVars, KindVars, DefVars)
tyPairConvertor :: TheoryEncoding -> TypePair -> Maybe OneConvert
tyPairConvertor encode (t1,t2,ct) = do
  (t1Sexp, tvars1, kvars1, df1) <- tyConvertor encode t1
  (t2Sexp, tvars2, kvars2, df2) <- tyConvertor encode t2
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

mkTyVarConst :: TheoryEncoding -> TyVar -> Maybe (SExpr, KindVars)
mkTyVarConst encode tv = do
  tvKindConv <- kindConvertor encode (tyVarKind tv)
  let kindStr = fst tvKindConv
  let kindVars = snd tvKindConv
  let name = show $ getUnique tv
  let smtStr = "(declare-const " ++ name ++ " " ++ kindStr ++ ")"
  return (SMT.Atom smtStr, kindVars)


monadMap :: Monad m => (a -> m b) -> [a] -> m [b]
monadMap _ [] = return []
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
  ClassPred cls (_: t1 : t2 : _) ->
    case cls == disEqCls of
      True -> Just (t1,t2,ct)
      False -> Nothing
  _ -> Nothing





----------------------------------------------------------
-- END Extraction
----------------------------------------------------------





----------------------------------------------------------
-- Type -> SExpr Conversion
----------------------------------------------------------


-- Recall: Type/KindVars = [TyVar]

tyConvertor ::
  TheoryEncoding -> Type -> Maybe (SExpr, TypeVars, KindVars, DefVars)
tyConvertor encode ty = do
  (strExp, tvars, kvars, defvars) <- innerTyConv encode ty
  return (SMT.Atom strExp, tvars, kvars, defvars)

innerTyConv ::
  TheoryEncoding -> Type -> Maybe (String, TypeVars, KindVars, DefVars)
innerTyConv encode ty = case tryTyVarConvert ty of
  Just (varNm, var) -> Just (varNm, [var], [], [])
  Nothing -> tryTyTheories encode ty

-- (1)
tryTyVarConvert :: Type -> Maybe (String, TyVar)
tryTyVarConvert ty = do
  tyvar <- getTyVar_maybe ty
  () <- assertIsSkolem tyvar
  let tvarName = show $ getUnique tyvar
  return (tvarName, tyvar)
  where
    assertIsSkolem = const $ Just ()
    -- Ignored for now:

-- (2)
tryTyTheories ::
  TheoryEncoding -> Type -> Maybe (String, TypeVars, KindVars, DefVars)
tryTyTheories encode@(TheoryEncoding {typeConvs = tconvs}) ty =
  case tryThese tconvs ty of
    -- TODO: declarations ignored:
    Just (TyConvCont types kinds strMaker _) -> do
      recurTypes <- vecMapAll (innerTyConv encode) types
      recurKinds <- vecMapAll (kindConvertor encode) kinds
      let filledTyHoles = vecMap (\(a,_,_,_) -> a) recurTypes
      let filledKdHoles = vecMap fst recurKinds
      let mkList = concat . vecMapList id
      let tyHoleTyVars = mkList $ vecMap (\(_,b,_,_) -> b) recurTypes
      let tyHoleKVars = mkList $ vecMap (\(_,_,c,_) -> c) recurTypes
      let defVars = mkList $ vecMap (\(_,_,_,d) -> d) recurTypes
      let kHoleKVars = mkList $ vecMap snd recurKinds
      let kVars = tyHoleKVars ++ kHoleKVars
      let convertedType = strMaker filledTyHoles filledKdHoles
      return (convertedType, tyHoleTyVars, kVars, defVars)
    Nothing -> defaultTyConv encode ty


tryThese :: [a -> Maybe b] -> a -> Maybe b
tryThese [] _ = Nothing
tryThese (f:fs) a = case f a of
  Nothing -> tryThese fs a
  Just b -> Just b



-- (3) From here, we are assuming the equational theory of Type 
-- is syntactic.
defaultTyConv ::
  TheoryEncoding -> Type -> Maybe (String, TypeVars, KindVars, DefVars)
defaultTyConv encode ty =
  case getTyVar_maybe ty of
    -- we redo type var checking b/c
    -- trivialFun & trivialTyCon recursivly call this fn
    Just tyvar -> let strTy = show $ getUnique tyvar
      in Just (strTy, [], [], [tyvar])
    Nothing -> defaultFunTyConvert encode ty


defaultFunTyConvert ::
  TheoryEncoding -> Type -> Maybe (String, TypeVars, KindVars, DefVars)
defaultFunTyConvert encode ty = case splitFunTy_maybe ty of
  Nothing -> defaultTyConConv encode ty
  Just (tyIn, _) -> do
    (strIn, tvs1, kvs1, df1) <- defaultTyConv encode tyIn
    (strOut, tvs2, kvs2, df2) <- defaultTyConv encode tyIn
    let smtStr = applyStr strIn strOut
    return (smtStr, tvs1 ++ tvs2, kvs1 ++ kvs2, df1 ++ df2)

applyStr :: String -> String -> String
applyStr strIn strOut =
  "(apply (apply (lit \"->\") " ++ strIn ++ ") " ++ strOut ++ ")"


defaultTyConConv ::
  TheoryEncoding -> Type -> Maybe (String, TypeVars, KindVars, DefVars)
defaultTyConConv encode ty = do
  (tcon, types) <- splitTyConApp_maybe ty
  case types of
    [] -> let smtStr = "(lit \"" ++ (show $ getUnique tcon) ++ "\")"
      in Just (smtStr, [], [], [])
    (_:_) -> do
      let tconString = "(lit \"" ++ (show $ getUnique tcon) ++ "\")"
      (strConvTypes, tv, kv, dv) <- maybeGetDefaultConvs encode types
      let smtString = foldl makeSExprApp tconString strConvTypes
      return (smtString, tv, kv, dv)

maybeGetDefaultConvs ::
  TheoryEncoding -> [Type] -> Maybe ([String], TypeVars, KindVars, DefVars)
maybeGetDefaultConvs _  [] = Just ([],[],[],[])
maybeGetDefaultConvs encode (x:xs) = do
  (strConv, tvars, kvars, defvars) <- defaultTyConv encode x
  (strConvs, tvars', kvars', defvars') <- maybeGetDefaultConvs encode xs
  let tv = tvars ++ tvars'
  let kv = kvars ++ kvars'
  let dv = defvars ++ defvars'
  return (strConv:strConvs, tv, kv, dv)


makeSExprApp :: String -> String -> String
makeSExprApp func arg = "(apply " ++ func ++ " " ++ arg ++ ")"



kindConvertor :: TheoryEncoding -> Kind -> Maybe (String, KindVars)
kindConvertor encode kind = case getTyVar_maybe kind of
  Just tvar -> let name = "Sort" ++ (show $ getUnique tvar)
    in Just (name, [tvar])
  Nothing -> tryKTheories encode kind

tryKTheories :: TheoryEncoding -> Kind -> Maybe (String, KindVars)
tryKTheories encode@(TheoryEncoding {kindConvs = kconvs}) kind =
  case tryThese kconvs kind of
    Nothing -> Just ("Type", []) -- kind defaulting
    Just (KdConvCont kholes strMaker) -> do
      recur <- vecMapAll (kindConvertor encode) kholes
      let filledHoles = vecMap fst recur
      let recurKVars = concat $ vecMapList id $ vecMap snd recur
      let convertedKind = strMaker filledHoles
      return (convertedKind, recurKVars)


----------------------------------------------------------
-- END: Type -> SExpr Conversion
----------------------------------------------------------


