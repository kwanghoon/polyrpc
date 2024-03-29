{-# LANGUAGE DeriveDataTypeable, DeriveGeneric #-}

module Surface where

import Location
import Type

--------------------------------------------
-- The design of surface syntax (Ver.0.1) --
--------------------------------------------
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

  (2-2) e = \a: x1 ... xn. and ty != {l}. ... and only -> types (not -Loc->) occurring in ty

   cs : forall a. a -> List a -> List a = \client: w lst. Cons w lst;
   ==>
   cs : forall a. client: a -> List a -> List a = \client: w lst. Cons w lst;
   ==>
   cs : forall a. a -client-> List a -client-> List a = \client: w lst. Cons w lst;


  cf. LExpr -> \\ Location : Identifiers . LExpr


(3) Located function types 'Loc: A -> B' is replaced by A' -Loc-> B'
    where A' is (Loc: A) and B' is (Loc: B).  though the surface
    syntax only allows Loc: in the beginning of types.

  cf. Type -> LocatedFunType

      LocatedFunType -> FunType
      LocatedFunType -> Location : FunType


  (3-1) You can use location variables after location abstractions with them.

  cf. s_five
        : {l1}. forall a b c. l1: ({l2}. l2: a -> b -> c) -> ({l3}. l3: a -> b) -> a -> c
        = \f g x. f x (g x)

  (3-2) The replacement of locations after Loc: will stop at another
        Loc': as can be understood in the above example.

  (3-3) In data type declarations, you may have to write client: more than once.

  cf. data Page a e = Page a ( client: a -> Html e) ( client: e -> a -> a ) String; 
           // Todo: client: a -> Html e and client: e -> a -> a 
           //   vs. client: Page a (a -> Html e) (e -> a -> a) 
           //   vs. Page {client} a e ???


(4) In datatype declarations,

 (4-1) No function types and no location abstractions

   [] (no changes)

   data List a = Nil | Cons a (List a)

 (4-2) Location abstractions 

   [] (no changes)

   data Stream {l} a =  SNil | SCons a (Unit -l-> Stream {l} a);

   cf. data Stream a {l} is not allowed. Do we need to allow it?

 (4-3) No location abstractions and all annotated function types

   [] (no changes)

   data Attr a = Property String String | Attribute String String | ...
               | ValueBind String (String -client-> a);

   cf. In the example, location variables would be unbound if they
       occur in the position of client.

 (4-4) No location abstractions and some unannotated function types and
       other annotated function types.

   [] (syntax error)

   Rationale: Using located function types means programmers know how
              to fix it themselves. No clever trick is provided by the
              compiler in the case. Thes simplest is the best!

   cf. A possible solution would be as follows:

      [] All the unannotated functions are

      [] All occurrences of D A1 ... Ak in types should be replaced by D {Loc} A1 ... Ak.
         (This requires a global change!)

      data D a1 ... ak = ... | Ci ... (Ai -> Bi) ... | Cj ... (Aj -Loc-> Bj) ...| ...

      ===>

      data D {l} a1 ... ak = ... | Ci ... (l: Ai -> Bi) ... | Cj ... (Aj -Loc-> Bj) ...| ...

   We guess that datatypes rarely use function types directly?!

(5) l: A -Loc->B

  (syntax error)

(6) When there occurs unannotated types after (1)-(5)

  (syntax error)

-}

-- For parsing
noLocName = "$empty"  -- Just to represent A -> B by A -$NoLoc-> B

defaultLocVarName = "$l" -- '$' cannot be written in the surface syntax.

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
    anno loc (FunType ty1 (Location loc0) ty2) = FunType (anno loc ty1) (Location loc0) (anno loc ty2)
    anno loc (FunType ty1 (LocVar name) ty2)
      | cond name = FunType (anno loc ty1) loc (anno loc ty2)
      | otherwise = FunType (anno loc ty1) (LocVar name) (anno loc ty2) -- Must not happen!!
    anno loc (TypeAbsType xs ty) = TypeAbsType xs (anno loc ty)
    anno loc (LocAbsType ls ty) = LocAbsType ls (anno loc ty)
    anno loc (ConType d locs tys) = ConType d locs (map (anno loc) tys)


isTyfromSingleWorld :: Type -> Bool
isTyfromSingleWorld (TypeVarType x) = True
isTyfromSingleWorld (TupleType tys) = and (map isTyfromSingleWorld tys)
isTyfromSingleWorld (FunType ty1 loc ty2) =
  isTyfromSingleWorld ty1
  && isTyfromSingleWorld ty2
  && isLocfromSingleWorld loc
isTyfromSingleWorld (TypeAbsType xs ty) = isTyfromSingleWorld ty
isTyfromSingleWorld (LocAbsType ls ty) = False
isTyfromSingleWorld (ConType d locs tys) = null locs && and (map isTyfromSingleWorld tys)

isLocfromSingleWorld (Location _) = False
isLocfromSingleWorld (LocVar name)
  | name == noLocName = True
  | otherwise = False
