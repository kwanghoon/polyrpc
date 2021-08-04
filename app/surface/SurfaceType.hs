{-# LANGUAGE DeriveDataTypeable, DeriveGeneric #-}

module SurfaceType where

import Location
import Type

-- Surface syntax
{-

(1) In types,

     - use '-Loc->' and '->' where the latter must be replaced somehow
       by the following rules.

     - use location abstraction as '{l1 ... lk}. ty'.

     - 'Loc: function type' for annotating Loc to multiple function types

    In terms,

     - '\client: x1 ... xn. e' or
       '\x1 ... xn. e'

(2) In function declaration bindings f : ty = e

  (2-1) e = \x1 ... xn. and ty != {l}. ...  and only -> types (not -Loc->) occurring in ty

   mapWithCount : forall a b. Int -> (a -> Int -> b) -> List a -> List b = \idx f xs. ...
   ==>
   mapWithCount : {l} forall a b. l: Int -> (a -> Int -> b) -> List a -> List b = \idx f xs. ...
   ==>
   mapWithCount : {l} forall a b. Int -l-> (a -l-> Int -l-> b) -l-> List a -l-> List b = \idx f xs. ...

  (2-2) e = \{a} x1 ... xn. and ty != {l}. ... and only -> types (not -Loc->) occurring in ty

   mapWithCount : forall a b. Int -> (a -> Int -> b) -> List a -> List b = \idx f xs. ...
   ==>
   mapWithCount : forall a b. client: Int -> (a -> Int -> b) -> List a -> List b = \idx f xs. ...
   ==>
   mapWithCount : forall a b. Int -client-> (a -client-> Int -client-> b) -client-> List a -client-> List b = \idx f xs. ...


(3) Located function types 'Loc: A -> B' is replaced by A' -Loc B'
    where A' is (Loc: A) and B' is (Loc: B).  though the surface
    syntax only allows Loc: in front of function types.

(4) In datatype declarations,

 (4-1) No function types and no location abstractions

   [] (no changes)

   data List a = Nil | Cons a (List a)

 (4-2) Location abstractions 

   [] (no changes)

   data Stream {l} a =  SNil | SCons a (Unit -l-> Stream {l} a);


 (4-3) No location abstractions and all annotated function types

   [] (no changes)

   data Attr a = Property String String | Attribute String String | ...
               | ValueBind String (String -client-> a);


 (4-4) No location abstractions and some unannotated function types and
       other annotated function types.

   [] (syntax error)

   A possible solution:

      [] All the unannotated functions are

      [] All occurrences of D A1 ... Ak in types should be replaced by D {Loc} A1 ... Ak.
         (This requires a global change!)

      data D a1 ... ak = ... | Ci ... (Ai -> Bi) ... | Cj ... (Aj -Loc-> Bj) ...| ...

      ===>

      data D {l} a1 ... ak = ... | Ci ... (l: Ai -> Bi) ... | Cj ... (Aj -Loc-> Bj) ...| ...

   We guess that datatypes are rarely using functions types directly!

(5) l: A -Loc->B

  (syntax error)

(6) When there occurs unannotated types after (1)-(5)

  (syntax error)

-}

-- For parsing
noLocName = "$empty"  -- Just to represent A -> B by A -$NoLoc-> B

--defaultLocVarName = "$l" -- '$' cannot be written in the surface syntax.

getLocFromMaybe :: Maybe Location -> Location
getLocFromMaybe (Just loc) = loc 
getLocFromMaybe Nothing    = LocVar noLocName -- defaultLocVarName

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
