{-# LANGUAGE DeriveDataTypeable, DeriveGeneric #-}

module SurfaceType where

import Location
import Type

-- For parsing
noLocName = "$NoLoc"  -- Just to represent A -> B by A -$NoLoc-> B

getLocFromMaybe :: Maybe Location -> Location
getLocFromMaybe (Just loc) = loc 
getLocFromMaybe Nothing    = LocVar defaultLocVarName

defaultLocVarName = "$l" -- '$' cannot be written in the surface syntax.

annotateLoc :: Maybe Location -> Type -> Type
annotateLoc maybeLoc ty = annoOnCond (\_ -> True) maybeLoc ty

annotateLocOnNoName :: Maybe Location -> Type -> Type
annotateLocOnNoName maybeLoc ty = annoOnCond (noLocName==)  maybeLoc ty

annoOnCond :: (String -> Bool) -> Maybe Location -> Type -> Type
annoOnCond cond maybeLoc ty =
  case maybeLoc of
    Just loc -> anno loc ty
    Nothing -> ty
  where
    anno loc (TypeVarType x) = TypeVarType x
    anno loc (TupleType tys) = TupleType (map (anno loc) tys)
    anno loc (FunType ty1 (Location _) ty2) = FunType (anno loc ty1) loc (anno loc ty2)
    anno loc (FunType ty1 (LocVar name) ty2)
      | cond name = FunType (anno loc ty1) loc (anno loc ty2)
      | otherwise = FunType (anno loc ty1) (LocVar name) (anno loc ty2)
    anno loc (TypeAbsType xs ty) = TypeAbsType xs (anno loc ty)
    anno loc (LocAbsType ls ty) = LocAbsType ls (anno loc ty)
    anno loc (ConType d locs tys) = ConType d locs (map (anno loc) tys)
