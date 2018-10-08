{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}

module ThoralfPlugin.Convert where

import Data.Maybe ( mapMaybe, catMaybes )
import qualified Data.Map as M
import qualified Data.Set as S
import qualified SimpleSMT as SMT
import Data.Semigroup
import Control.Monad.Reader
import Prelude


-- GHC API imports:
import GhcPlugins ( getUnique )
import TcRnTypes ( Ct, ctPred )
import Class ( Class(..) )
import TcType ( Kind, tcGetTyVar_maybe )
import Var ( TyVar )
import Type ( Type, PredTree (..), EqRel (..), getTyVar_maybe
            , splitTyConApp_maybe, splitFunTy_maybe
            , classifyPredType, tyVarKind )


-- Internal imports
import ThoralfPlugin.Encode.TheoryEncoding
import Data.Vec



-- * Data Definitions
--------------------------------------------------------------------------------


-- ** Core Types

-- | The input needed to convert 'Ct' into smt expressions.
-- We need the class for dis equality, and an encoding of a collection of
-- theories.
data EncodingData where
  EncodingData ::
    { encodeDisEq :: Class
    , encodeTheory :: TheoryEncoding
    } -> EncodingData


-- | The output of converting constraints. We have a list of converted
-- constraints as well as a list of declarations. These declarations are
-- variable declarations as well as function symbols with accompanying
-- defining assert statements.
data ConvCts where
  ConvCts ::
    { convEquals :: [(SExpr, Ct)]
    , convDeps :: [SExpr]
    } -> ConvCts


-- | Since our encoding data is passed around as a constant state, we put
-- it in a reader monad. Of course, conversion could fail, so we transform
-- from a Maybe monad.
type ConvMonad a = ReaderT EncodingData Maybe a




-- ** Basic Definitions

-- | The type of smt expressions.
type SExpr = SMT.SExpr



-- * Convert Function
--------------------------------------------------------------------------------

convert :: EncodingData -> [Ct] -> Maybe ConvCts
convert encodingData cts = runReaderT (conv cts) encodingData


conv :: [Ct] -> ConvMonad ConvCts
conv cts = do
  EncodingData disEqClass _ <- ask
  let disEquals = extractDisEq disEqClass cts
  let equals = extractEq cts
  convDisEqs <- mapSome $ fmap convPair (map fst disEquals)
  convEqs <- mapSome $ fmap convPair (map fst equals)

  let deps = mconcat $ map snd convDisEqs ++ map snd convEqs
  decls <- convertDeps deps

  let eqExprs = map (mkEqExpr . fst) convEqs
  let disEqExprs = map (mkDisEqExpr . fst) convDisEqs
  let matchingCts = map snd $ disEquals ++ equals
  --guard (length matchingCts == length (disEqExprs ++ eqExprs))
  let convPairs = zip (disEqExprs ++ eqExprs) matchingCts
  return $ ConvCts convPairs decls

  where

  convPair :: (Type, Type) -> ConvMonad ((SExpr, SExpr), ConvDependencies)
  convPair (t1, t2) = do
    (t1', deps1) <- convertType t1
    (t2', deps2) <- convertType t2
    let sexpr = SMT.Atom
    let convertedPair = (sexpr t1', sexpr t2')
    return (convertedPair, deps1 <> deps2)


  mkEqExpr :: (SExpr, SExpr) -> SExpr
  mkEqExpr (s1,s2) = SMT.eq s1 s2

  mkDisEqExpr :: (SExpr, SExpr) -> SExpr
  mkDisEqExpr (s1,s2) = (SMT.not $ SMT.eq s1 s2)

  mapSome :: [ConvMonad a] -> ConvMonad [a]
  mapSome xs = do
    state <- ask
    let maybeVals = map (`runReaderT` state) xs
    return $ catMaybes maybeVals




-- ** Extraction
--------------------------------------------------------------------------------

extractEq :: [Ct] -> [((Type, Type), Ct)]
extractEq = mapMaybe maybeExtractTyEq

extractDisEq :: Class -> [Ct] -> [((Type, Type), Ct)]
extractDisEq cls = mapMaybe (maybeExtractTyDisEq cls) where


maybeExtractTyDisEq :: Class -> Ct -> Maybe ((Type, Type), Ct)
maybeExtractTyDisEq disEqCls ct = do
  let predTree = classifyPredType $ ctPred ct
  ClassPred class' (_: t1 : t2 : _) <- return predTree
  guard (class' == disEqCls)
  return ((t1,t2),ct)

maybeExtractTyEq :: Ct -> Maybe ((Type, Type), Ct)
maybeExtractTyEq ct = do
  let predTree = classifyPredType $ ctPred ct
  case predTree of
    EqPred NomEq t1 t2 -> return ((t1,t2),ct)
    _ -> Nothing


  {-
  return ((simpIfCan t1, simpIfCan t2), ct) where

  simpIfCan :: Type -> Type
  simpIfCan t = case coreView t of
    Just t' -> t'
    Nothing -> t -}


-- ** Converting the Dependencies
----------------------------------------


convertDeps :: ConvDependencies -> ConvMonad [SExpr]
convertDeps (ConvDeps tyvars' kdvars' defvars' decs) = do
  let nub = S.toList . S.fromList
  let tyvars = nub tyvars'
  let kdvars = nub kdvars'
  let defvars = nub defvars'
  (EncodingData _ theories) <- ask
  let mkPred = tyVarPreds theories
  let tvPreds = foldMap (fmap SMT.Atom) $ mapMaybe mkPred tyvars

  convertedTyVars <- traverse convertTyVars tyvars
  let tyVarExprs = map fst convertedTyVars
  let kindVars = nub $ concatMap snd convertedTyVars ++ kdvars
  let kindExprs = map mkSMTSort kindVars
  let defExprs = map mkDefaultSMTVar defvars
  decExprs <- convertDecs decs
  -- Order matters:
  let varExprs = kindExprs ++ tyVarExprs ++ defExprs
  let otherExprs = decExprs ++ tvPreds
  let exprs = varExprs ++ otherExprs
  return exprs


-- | Converting Local Declarations
convertDecs :: [Decl] -> ConvMonad [SExpr]
convertDecs ds = do
  let assocList = map (\(Decl k v) -> (k,v)) ds
  let ourMap = M.fromList assocList
  let uniqueDecs = foldMap snd $ M.toList ourMap
  return $ map SMT.Atom uniqueDecs where


mkDefaultSMTVar :: TyVar -> SExpr
mkDefaultSMTVar tv = let
  name = show $ getUnique tv
  smtStr = "(declare-const " ++ name ++ " Type)"
  in SMT.Atom smtStr

mkSMTSort :: TyVar -> SExpr
mkSMTSort tv = let
  name = "Sort" ++ (show $ getUnique tv)
  smtStr = "(declare-sort " ++ name ++ ")"
  in SMT.Atom smtStr


-- | Kind variables are just type variables
type KdVar = TyVar
convertTyVars :: TyVar -> ConvMonad (SExpr, [KdVar])
convertTyVars tv = do
  (smtSort, kindVars) <- convertKind $ tyVarKind tv
  let tvId = show $ getUnique tv
  let smtVar = "(declare-const " ++ tvId ++ " " ++ smtSort ++ ")"
  return (SMT.Atom smtVar, kindVars)




-- * Converting A Single Type
--------------------------------------------------------------------------------


-- ** Type Conversion Data
----------------------------------------

-- | A Type is converted into a string which is a valid SMT term, if the
-- dependencies are converted properly and sent to the solver before the
-- term is mentioned.
type ConvertedType = (String, ConvDependencies)

-- | These are pieces of a type that need to be converted into
-- SMT declarations or definitions in order for the converted
-- type to be well sorted or correct.
data ConvDependencies where
  ConvDeps ::
    { convTyVars :: [TyVar] -- Type variables for a known theory
    , convKdVars :: [TyVar] -- Kind variables for unknown theories
    , convDefVar :: [TyVar] -- Type variables for default, syntactic theories
    , convDecs   :: [Decl]  -- SMT declarations specific to some converted type
    } -> ConvDependencies

noDeps :: ConvDependencies
noDeps = mempty

data Decl where
  Decl ::
    { decKey :: (String, String) -- ^ A unique identifier
    , localDec :: [String]       -- ^ A list of local declarations
    } -> Decl

type Hash = String


instance Semigroup ConvDependencies where
  (ConvDeps a b c d) <> (ConvDeps e f g h) =
    ConvDeps (a ++ e) (b ++ f) (c ++ g) (d ++ h)

instance Monoid ConvDependencies where
  mempty = ConvDeps [] [] [] []
  mappend = (<>)



-- ** Converting A Type
----------------------------------------



convertType :: Type -> ConvMonad ConvertedType
convertType ty =
  case tyVarConv ty of
    Just (smtVar, tyvar) ->
      return  (smtVar, noDeps {convTyVars = [tyvar]})
    Nothing -> tryConvTheory ty

tyVarConv :: Type -> Maybe (String, TyVar)
tyVarConv ty = do
  tyvar <- tcGetTyVar_maybe ty
  -- Not checking for skolems.
  -- See doc on "dumb tau variables"
  let isSkolem = True
  guard isSkolem
  let tvarStr = show $ getUnique tyvar
  return (tvarStr, tyvar)


tryConvTheory :: Type -> ConvMonad ConvertedType
tryConvTheory ty = do
  EncodingData _ theories <- ask
  let tyConvs = typeConvs theories
  case tryFns tyConvs ty of
    Just (TyConvCont tys kds cont decs) -> do
      recurTys <- vecMapAll convertType tys
      recurKds <- vecMapAll convertKind kds
      (decls, decKds) <- convDecConts decs
      let convTys = fmap fst recurTys
      let convKds = fmap fst recurKds
      let converted = cont convTys convKds
      let tyDeps = foldMap snd recurTys
      let kdVars = foldMap snd recurKds ++ decKds
      let deps = addDepParts tyDeps kdVars decls
      return (converted, deps)
    Nothing -> defaultConvTy ty

addDepParts :: ConvDependencies -> [KdVar] -> [Decl] -> ConvDependencies
addDepParts (ConvDeps t k d decl) ks decls =
  ConvDeps t (k ++ ks) d (decl ++ decls)

convDecConts :: [DecCont] -> ConvMonad ([Decl], [KdVar])
convDecConts dcs = do
  decConts <- traverse convDecCont dcs
  let decls = map fst decConts
  let kdVars = concatMap snd decConts
  return (decls, kdVars) where

  convDecCont :: DecCont -> ConvMonad (Decl, [KdVar])
  convDecCont (DecCont kholes declName cont) = do
   recur <- vecMapAll convertKind kholes
   let kConvs = fmap fst recur
   let declKey = (declName, foldMap id kConvs)
   let kdVars = foldMap snd recur
   let decl = Decl declKey (cont kConvs)
   return (decl, kdVars)


defaultConvTy :: Type -> ConvMonad ConvertedType
defaultConvTy ty = do
  (convertedTy, defVars) <- lift (defConvTy ty)
  return (convertedTy, noDeps {convDefVar = defVars})

defConvTy :: Type -> Maybe (String, [TyVar])
defConvTy = tryFns [defTyVar, defFn, defTyConApp] where

  defTyVar :: Type -> Maybe (String, [TyVar])
  defTyVar ty = do
    tv <- getTyVar_maybe ty
    return ( show $ getUnique tv, [tv])

  defFn :: Type -> Maybe (String, [TyVar])
  defFn ty = do
    (fn, arg) <- splitFunTy_maybe ty
    (fnStr, tv1) <- defConvTy fn
    (argStr, tv2) <- defConvTy arg
    let smtStr = fnDef fnStr argStr
    return (smtStr, tv1 ++ tv2)

  fnDef :: String -> String -> String
  fnDef strIn strOut =
    "(apply (apply (lit \"->\") " ++
      strIn ++ ") " ++ strOut ++ ")"

  defTyConApp :: Type -> Maybe (String, [TyVar])
  defTyConApp ty = do
    (tcon, tys) <- splitTyConApp_maybe ty
    recur <- traverse defConvTy tys
    let defConvTys = map fst recur
    let tvars = foldMap snd recur
    let convTcon = "(lit \"" ++ (show $ getUnique tcon) ++ "\")"
    let converted = foldl appDef convTcon defConvTys
    return (converted, tvars)

  appDef :: String -> String -> String
  appDef f x = "(apply " ++ f ++ " " ++ x ++ ")"






-- * Converting A Single Kind
------------------------------------------------------------------------------


-- | Converts a Kind into a String and some kind variables
convertKind :: Kind -> ConvMonad (String, [KdVar])
convertKind kind =
  case getTyVar_maybe kind of
    Just tvar ->
      return ("Sort" ++ (show $ getUnique tvar), [tvar])
    Nothing -> convKindTheories kind

convKindTheories :: Kind -> ConvMonad (String, [KdVar])
convKindTheories kind = do
  EncodingData _ theories <- ask
  let kindConvFns = kindConvs theories
  case tryFns kindConvFns kind of
    Nothing -> return ("Type", []) -- Kind defaulting
    Just (KdConvCont kholes kContin) -> do
      recur <- vecMapAll convertKind kholes
      let convHoles = fmap fst recur
      let holeVars = foldMap snd recur
      return (kContin convHoles, holeVars)




-- * A Common Helper Function

-- | In order, try the functions.
tryFns :: [a -> Maybe b] -> a -> Maybe b
tryFns [] _ = Nothing
tryFns (f:fs) a = case f a of
  Nothing -> tryFns fs a
  Just b -> Just b




