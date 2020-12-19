{-# LANGUAGE DeriveDataTypeable, DeriveGeneric #-}

module Type where

import Prim
import Data.Char
import Data.Set(Set)
import qualified Data.Set as S
-- For aeson
-- import GHC.Generics
-- import Data.Aeson
import Text.JSON.Generic

import Naming
import Pretty
import Location

data Type =
    TypeVarType TypeVar
  | TupleType [Type]
  | FunType Type Location Type
  | TypeAbsType [TypeVar] Type
  | LocAbsType [LocationVar] Type
  | ConType String [Location] [Type]
  deriving (Show, Typeable, Data, Eq)

type TypeVar = String

singleTypeAbsType (TypeAbsType [] expr) = expr
singleTypeAbsType (TypeAbsType [a] expr) = TypeAbsType [a] expr
singleTypeAbsType (TypeAbsType (a:as) expr) = TypeAbsType [a] (singleTypeAbsType (TypeAbsType as expr))
singleTypeAbsType other = other

singleLocAbsType (LocAbsType [] expr) = expr
singleLocAbsType (LocAbsType [a] expr) = LocAbsType [a] expr
singleLocAbsType (LocAbsType (a:as) expr) = LocAbsType [a] (singleLocAbsType (LocAbsType as expr))
singleLocAbsType other = other

mkFunType :: [Type] -> Location -> Type -> Type
mkFunType [] loc retty = retty
mkFunType (ty:tys) loc retty = FunType ty loc (mkFunType tys loc retty)

--
-- For aeson
-- instance ToJSON Location where
-- instance ToJSON Type where

-- Names
isTypeName (c:s) = isUpper c
isTypeName _     = False

isTypeVarName (c:s) = isLower c
isTypeVarName _ = False

isLocationVarName (c:s) = isLower c
isLocationVarName _ = False

isBindingName (c:s) = isLower c
isBindingName _     = False

isConstructorName (c:s) = isUpper c
isConstructorName _     = False


--
primType tyname = ConType tyname [] []

bool_type = primType boolType
int_type  = primType intType
unit_type = primType unitType
string_type = primType stringType


--
doSubstOne :: String -> Type -> Type -> Type
doSubstOne x ty (TypeVarType y)
  | x==y = ty
  | otherwise = (TypeVarType y)
doSubstOne x ty (TupleType tys) =
  TupleType (map (doSubstOne x ty) tys)
doSubstOne x ty (FunType argty loc retty) =
  FunType (doSubstOne x ty argty) loc (doSubstOne x ty retty)
doSubstOne x ty (TypeAbsType tyvars bodyty)
  | elem x tyvars = (TypeAbsType tyvars bodyty)
  | otherwise = (TypeAbsType tyvars (doSubstOne x ty bodyty))
doSubstOne x ty (LocAbsType locvars bodyty) =
  LocAbsType locvars (doSubstOne x ty bodyty)
doSubstOne x ty (ConType name locs tys) =
  ConType name locs (map (doSubstOne x ty) tys)

doSubst :: [(String,Type)] -> Type -> Type
doSubst [] ty0 = ty0
doSubst ((x,ty):subst) ty0 = 
  doSubst subst (doSubstOne x ty ty0)

--
doSubstLocOne :: String -> Location -> Type -> Type
doSubstLocOne x loc (TypeVarType y) = (TypeVarType y)
doSubstLocOne x loc (TupleType tys) =
  TupleType (map (doSubstLocOne x loc) tys)
doSubstLocOne x loc (FunType argty loc0 retty) =
  FunType (doSubstLocOne x loc argty)
    (doSubstLocOverLoc x loc loc0) (doSubstLocOne x loc retty)
doSubstLocOne x loc (TypeAbsType tyvars bodyty) =
  TypeAbsType tyvars (doSubstLocOne x loc bodyty)
doSubstLocOne x loc (LocAbsType locvars bodyty)
  | elem x locvars = LocAbsType locvars bodyty
  | otherwise = LocAbsType locvars (doSubstLocOne x loc bodyty)
doSubstLocOne x loc (ConType name locs tys) =
  ConType name (map (doSubstLocOverLoc x loc) locs) (map (doSubstLocOne x loc) tys)


doSubstLoc :: [(String, Location)] -> Type -> Type
doSubstLoc [] ty = ty
doSubstLoc ((x,loc):substLoc) ty =
  doSubstLoc substLoc (doSubstLocOne x loc ty)

locSubst :: Location -> LocationVar -> Type -> Type 
locSubst loc l ty = doSubstLocOne l loc ty

locSubsts :: [Location] -> [LocationVar] -> Type -> Type
locSubsts locs ls ty = doSubstLoc (zip ls locs) ty

--
equalType :: Type -> Type -> Bool
equalType ty1 ty2 = equalTypeWithFreshness [1..] ty1 ty2

equalTypeWithFreshness ns (TypeVarType x) (TypeVarType y) = x==y

equalTypeWithFreshness ns (TupleType tys1) (TupleType tys2) =
  and (map (uncurry (equalTypeWithFreshness ns)) (zip tys1 tys2))
  
equalTypeWithFreshness ns (FunType argty1 loc1 retty1) (FunType argty2 loc2 retty2) =
  equalTypeWithFreshness ns argty1 argty2 && equalLoc loc1 loc2 && equalTypeWithFreshness ns retty1 retty2
  
equalTypeWithFreshness ns (TypeAbsType tyvars1 ty1) (TypeAbsType tyvars2 ty2) =
  let len1 = length tyvars1
      len2 = length tyvars2
      newvars = map (TypeVarType . show) (take len1 ns)
      ns'     = drop len1 ns
  in len1==len2 && equalTypeWithFreshness ns' (doSubst (zip tyvars1 newvars) ty1) (doSubst (zip tyvars2 newvars) ty2)
     
equalTypeWithFreshness ns (LocAbsType locvars1 ty1) (LocAbsType locvars2 ty2) =
  let len1 = length locvars1
      len2 = length locvars2
      newvars = map (LocVar . show) (take len1 ns)
      ns'     = drop len1 ns
  in len1==len2 && equalTypeWithFreshness ns' (doSubstLoc (zip locvars1 newvars) ty1) (doSubstLoc (zip locvars2 newvars) ty2)

equalTypeWithFreshness ns (ConType name1 locs1 tys1) (ConType name2 locs2 tys2) =   
  name1==name2 && equalLocs locs1 locs2 && and (map (uncurry (equalTypeWithFreshness ns)) (zip tys1 tys2))

equalTypeWithFreshness ns ty1 ty2 = False

--
occur :: String -> Type -> Bool
occur x (TypeVarType y) = x==y
occur x (TupleType tys) = and (map (occur x) tys)
occur x (FunType argty loc retty) = occur x argty && occur x retty
occur x (ConType c locs tys) = and (map (occur x) tys)
occur x (TypeAbsType _ _) = False  -- ???
occur x (LocAbsType _ _) = False -- ???

unifyTypeOne :: Type -> Type -> Maybe [(String,Type)]
unifyTypeOne (TypeVarType x) (TypeVarType y)
  | x==y = Just []
  | otherwise = Just [(x, TypeVarType y)]
  
unifyTypeOne (TypeVarType x) ty
  | occur x ty = Nothing
  | otherwise = Just [(x,ty)]

unifyTypeOne ty (TypeVarType x)
  | occur x ty = Nothing
  | otherwise = Just [(x,ty)]

unifyTypeOne (TupleType tys1) (TupleType tys2) = unifyTypes tys1 tys2

unifyTypeOne (FunType argty1 loc1 retty1) (FunType argty2 loc2 retty2) =  -- loc1 and loc2 ??
  case unifyTypeOne argty1 argty2 of
    Nothing -> Nothing
    Just subst1 ->
      case unifyTypeOne (doSubst subst1 retty1) (doSubst subst1 retty2) of
        Nothing -> Nothing
        Just subst2 -> Just (subst1 ++ subst2)

unifyTypeOne (ConType c1 locs1 tys1) (ConType c2 locs2 tys2)  -- locs1, locs2 ???
  | c1==c2 = unifyTypes tys1 tys2
  | otherwise = Nothing

unifyTypeOne _ _ = Nothing   -- universal types and locations ???

unifyTypes :: [Type] -> [Type] -> Maybe [(String,Type)]
unifyTypes [] [] = Just []
unifyTypes (ty1:tys1) (ty2:tys2) =
  case unifyTypeOne ty1 ty2 of
    Nothing -> Nothing
    Just subst1 ->
      case unifyTypes (map (doSubst subst1) tys1) (map (doSubst subst1) tys2) of
        Nothing -> Nothing
        Just subst2 -> Just (subst1 ++ subst2)

-- | Is the type a Monotype?
monotype :: Type -> Maybe Type
monotype typ = case typ of
  TypeVarType v     -> Just $ TypeVarType v -- TVar and TExists
  TupleType tys     -> TupleType <$> mapM monotype tys
  FunType t1 loc t2 -> FunType <$> monotype t1 <*> Just loc <*> monotype t2
  TypeAbsType _ _   -> Nothing
  LocAbsType _ _    -> Nothing
  ConType c locs tys -> ConType c <$> Just locs <*> mapM monotype tys

-- | Any type is a Polytype since Monotype is a subset of Polytype
polytype :: Type -> Type
polytype typ = case typ of
  TypeVarType v  -> TypeVarType v   -- TVar and TExists
  TupleType tys  -> TupleType (map polytype tys)
  FunType t1 loc t2 -> FunType (polytype t1) loc (polytype t2)
  TypeAbsType v t    -> TypeAbsType v (polytype t)
  LocAbsType loc t  -> LocAbsType loc (polytype t)
  ConType c locs tys -> ConType c locs (map polytype tys)
        
-- Pretty

instance Pretty Type where
  bpretty d typ = case typ of
    TypeVarType v ->
      if cExists v
      then showParen (d > exists_prec) $
           showString $ "∃" ++ v
      else showString v
    TupleType tys ->
      showString "(" . showTuple tys . showString ")"
    FunType t1 loc t2 -> showParen (d > fun_prec) $
      bpretty (fun_prec + 1) t1 .
      showString " -" . bpretty d loc  . showString "-> " .
      bpretty fun_prec t2
    TypeAbsType vs t -> showParen (d > forall_prec) $
      showString "[" . showWithComma vs .
      showString "]. "      . bpretty forall_prec t
    LocAbsType ls t -> showParen (d > forall_prec) $
      showString "{" . showWithComma ls .
      showString "}. "      . bpretty forall_prec t
    ConType c ls tys ->
      showString c . showSpace (not (null ls)) (showLocs ls)
                   . showSpace (not (null tys)) (showTys tys)
    where
      exists_prec = 10
      forall_prec :: Int
      forall_prec = 1
      fun_prec    = 1

-- | typeSubst A α B = [A/α]B
typeSubst :: Type -> TypeVar -> Type -> Type
typeSubst t' v typ = doSubstOne v t' typ

typeSubsts :: [Type] -> [TypeVar] -> Type -> Type
typeSubsts ts' vs typ = doSubst (zip vs ts') typ


--
-- | The free type variables in a type
freeTVars :: Type -> Set TypeVar
freeTVars typ = case typ of
  TypeVarType v    -> S.singleton v
  TupleType tys    -> foldl mappend mempty (map freeTVars tys)
  FunType t1 _ t2  -> freeTVars t1 `mappend` freeTVars t2
  TypeAbsType vs t -> foldl (\set v -> S.delete v set) (freeTVars t) vs
  LocAbsType ls t  -> freeTVars t
  ConType c ls tys -> foldl mappend mempty (map freeTVars tys)

--
-- | The free location variables in a type
freeLVars :: Type -> Set LocationVar
freeLVars typ = case typ of
  TypeVarType v     -> mempty
  TupleType tys     -> foldl mappend mempty (map freeLVars tys)
  FunType t1 loc t2 -> freeLVars t1 `mappend` freeLVarsIn loc `mappend` freeLVars t2
  TypeAbsType vs ty -> freeLVars ty
  LocAbsType ls t   -> foldl (\set l -> S.delete l set) (freeTVars t) ls
  ConType c ls tys  -> foldl mappend mempty (map freeLVarsIn ls)
                         `mappend` foldl mappend mempty (map freeLVars tys)
