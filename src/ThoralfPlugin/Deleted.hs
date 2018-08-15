module ThoralfPlugin.Deleted where




-- Kind Conversion
-------------------------------------------------------------------------

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
-- Type -> SExpr Conversion
----------------------------------------------------------


type TypeVars = [TyVar]
type KindVars = [TyVar]
type DefVars = [TyVar] -- for defaulting: (declare-const lk3w Type)
type ParseResult = ([(SExpr, SExpr, Ct)], TypeVars, KindVars, DefVars)




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
  Just (tyIn, tyOut) -> do
    (strIn, tvs1, kvs1, df1) <- defaultTyConv encode tyIn
    (strOut, tvs2, kvs2, df2) <- defaultTyConv encode tyOut
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


----------------------------------------------------------
-- END: Type -> SExpr Conversion
----------------------------------------------------------


a









