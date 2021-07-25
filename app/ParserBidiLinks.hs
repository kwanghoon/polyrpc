module ParserBidiLinks where

-- | A parsimonius approach to location polymorphism

--   (1) A -> B   vs. A -Loc-> B
--   (2) \x1 ... xk @ Loc . e  vs. \x1 @ Loc1 ... xk @ Loc . e
--   (3) data D = Con ty1 ... tyn | ...
--       vs. data D = {l1 ... li} [a1 ... ak] Con ty1 ... tyn | ...
--   (4) forall a1 ... ak ty  vs.  [a1 ... ak] ty
--   (5) ty  vs {l1 ... li} ty
--   (6) ! expr  vs. ! {Loc} expr
--   (7) var := expr  vs. var := {Loc} expr

import CommonParserUtil
import Location
import Token
import Type
import Prim
import Literal
import Expr
import SurfaceType

parserSpec :: ParserSpec Token AST
parserSpec = ParserSpec
  {
    startSymbol = "TopLevel'",

    parserSpecList =
    [
      ("TopLevel' -> TopLevel", \rhs -> get rhs 1),

      {- Identifiers -}
      ("Identifiers -> identifier", \rhs -> toASTIdSeq [getText rhs 1] ),

      ("Identifiers -> identifier Identifiers",
        \rhs -> toASTIdSeq (getText rhs 1 : fromASTIdSeq (get rhs 2)) ),


      {- OptIdentifiers -}
      ("OptIdentifiers -> ", \rhs -> toASTIdSeq [] ),

      ("OptIdentifiers -> Identifiers", \rhs -> get rhs 1 ),


      {- IdentifierCommas -}
      ("IdentifierCommas -> identifier", \rhs -> toASTIdSeq [getText rhs 1] ),

      ("IdentifierCommas -> identifier , IdentifierCommas",
        \rhs -> toASTIdSeq (getText rhs 1 : fromASTIdSeq (get rhs 3)) ),


      {- OptIdentifierCommas -}
      ("OptIdentifierCommas -> ", \rhs -> toASTIdSeq [] ),

      ("OptIdentifierCommas -> IdentifierCommas", \rhs -> get rhs 1 ),


      {- Location -}
      ("Location -> identifier", \rhs -> toASTLocation (locOrVar (getText rhs 1)) ),


      {- Locations -}
      ("Locations -> Identifiers", \rhs ->
        toASTLocationSeq (map locOrVar (fromASTIdSeq (get rhs 1))) ),


      {- Type -}
      ("Type -> FunType", \rhs -> get rhs 1 ),

      -- No location abstraction types in the surface syntax:
      --  Type -> { Identifiers } . Type

      -- The syntax of abstraction types is changed:
      --  Type -> [ Identifiers ] . Type
      ("Type -> forall Identifiers . FunType", \rhs ->
        toASTType (singleTypeAbsType (TypeAbsType
                                              (fromASTIdSeq (get rhs 2))
                                              (fromASTType (get rhs 4)))) ),


      {- FunType -}
      ("FunType -> AppType", \rhs -> get rhs 1),

      ("FunType -> AppType -> FunType", \rhs ->
          let loc = SurfaceType.noLocName
          in  toASTType (FunType
                          (fromASTType (get rhs 1))
                          (locOrVar loc)
                          (fromASTType (get rhs 3))) ),


      {- AppType -}
      ("AppType -> AtomicType", \rhs -> get rhs 1),

      ("AppType -> AppType { Locations }", \rhs ->
          let locs = fromASTLocationSeq (get rhs 3) in
          case fromASTType (get rhs 1) of
            ConType name [] [] -> toASTType (ConType name locs [])
            ConType name [] tys ->
              error $ "[Parser] Not supported: types and then locations: " ++ show locs ++ " " ++ show tys
            ConType name locs' tys ->
              error $ "[Parser] Not supported: multiple locations" ++ name ++ " " ++ show locs' ++ " " ++ show locs
            TypeVarType name -> toASTType (ConType name locs []) -- Now this will never happen!
            ty ->
              error $ "[Parser] Not supported yet: " ++ show ty ++ " not ConType: " ++ show locs),

      -- Todo: Fix to delete [ and ]!!
      -- ("AppType -> AppType FunTypes", \rhs ->
      ("AppType -> AppType AtomicType", \rhs ->
          let ty = fromASTType (get rhs 2) in
          case fromASTType (get rhs 1) of
            ConType name locs tys -> toASTType (ConType name locs (tys ++ [ty]))
            -- ConType name locs tys' ->
            --   error $ "[Parser] Not supported: multiple types: " ++ name ++ " " ++ show tys' ++ " " ++ show tys
            TypeVarType name -> toASTType (ConType name [] [ty]) -- Now this will never happen!
            ty0 ->
              error $ "[Parser] Not supported yet: " ++ show ty0 ++ " not ConType: " ++ show ty),

      {- OptAtomicTypes -}
      ("OptAtomicTypes -> ", \rhs -> toASTTypeSeq [] ),

      ("OptAtomicTypes -> AtomicTypes", \rhs -> get rhs 1 ),
      
      {- AtomicTypes -}
      ("AtomicTypes -> AtomicType", \rhs -> toASTTypeSeq [fromASTType (get rhs 1)] ),

      ("AtomicTypes -> AtomicType AtomicTypes",
        \rhs -> toASTTypeSeq $ fromASTType (get rhs 1) : fromASTTypeSeq (get rhs 2) ),
      
      {- AtomicType -}
      ("AtomicType -> TupleType", \rhs -> get rhs 1 ),

      ("AtomicType -> ( Type )", \rhs -> get rhs 2 ),

      ("AtomicType -> identifier", \rhs -> toASTType (typeconOrVar (getText rhs 1)) ),

      
      {- TupleType -}
      ("TupleType -> ( )", \rhs -> toASTType (TupleType [] )),
      
      ("TupleType -> ( Type , TypeSeq )",
        \rhs -> toASTType (TupleType $
            (fromASTType (get rhs 2)) : (fromASTTypeSeq (get rhs 4))) ),


      {- TypeSeq -}
      ("TypeSeq -> Type", \rhs -> toASTTypeSeq [fromASTType (get rhs 1)] ),

      ("TypeSeq -> Type , TypeSeq",
        \rhs -> toASTTypeSeq $ fromASTType (get rhs 1) : (fromASTTypeSeq (get rhs 3)) ),


      {- FunTypes -}
      -- ("FunTypes -> FunType", \rhs -> toASTTypeSeq [fromASTType (get rhs 1)] ),

      -- ("FunTypes -> FunType FunTypes",
      --   \rhs -> toASTTypeSeq $ fromASTType (get rhs 1) : fromASTTypeSeq (get rhs 2) ),


      {- OptFunTypes -}
      -- ("OptFunTypes -> ", \rhs -> toASTTypeSeq [] ),

      -- ("OptFunTypes -> FunTypes", \rhs -> get rhs 1 ),


      {- TopLevel -}
      ("TopLevel -> Binding",
        \rhs -> toASTTopLevelDeclSeq [BindingTopLevel (setTop (fromASTBindingDecl (get rhs 1 )))] ),

      ("TopLevel -> Binding ; TopLevel",
        \rhs -> toASTTopLevelDeclSeq
            $ BindingTopLevel (setTop (fromASTBindingDecl (get rhs 1))) : fromASTTopLevelDeclSeq (get rhs 3) ),

      ("TopLevel -> DataTypeDecl",
        \rhs -> toASTTopLevelDeclSeq [DataTypeTopLevel (fromASTDataTypeDecl (get rhs 1))] ),

      ("TopLevel -> DataTypeDecl ; TopLevel",
        \rhs -> toASTTopLevelDeclSeq
            $ DataTypeTopLevel (fromASTDataTypeDecl (get rhs 1)) : (fromASTTopLevelDeclSeq (get rhs 3)) ),


      {- DataTypeDecl -}
      ("DataTypeDecl -> data identifier { identifiers } OptIdentifiers = DataTypeDeclRHS", \rhs ->
           let name = getText rhs 2
               locvars = fromASTIdSeq (get rhs 4)
               tyvars  = fromASTIdSeq (get rhs 6)
               (_,_,tycondecls) = fromASTTriple (get rhs 8)
           in toASTDataTypeDecl (DataType name locvars tyvars tycondecls)),

      ("DataTypeDecl -> data identifier OptIdentifiers = DataTypeDeclRHS", \rhs ->
           let name = getText rhs 2
               locvars = []
               tyvars  = fromASTIdSeq (get rhs 3)
               (_,_,tycondecls) = fromASTTriple (get rhs 5)
           in toASTDataTypeDecl (DataType name locvars tyvars tycondecls)),

      {- DataTypeDeclRHS -}
      -- Leave this later for investigating using GADT in the polymorphic RPC calculus!!
      ("DataTypeDeclRHS -> TypeConDecls", \rhs ->
           toASTTriple ([], [], fromASTTypeConDeclSeq (get rhs 1)) ),

      -- No location abstraction in data type declarations in the surface syntax:
      -- ("DataTypeDeclRHS -> { Identifiers } . DataTypeDeclRHS", \rhs ->
      --      let locvars = fromASTIdSeq (get rhs 2) in
      --      case fromASTTriple (get rhs 5) of
      --        ([], tyvars, tycondecls) -> toASTTriple (locvars, tyvars, tycondecls)
      --        (locvars', tyvars, tycondecls) ->
      --          error $ "[Parser] Not supported yet: multiple location abstractions: "
      --                      ++ show locvars' ++ " " ++ show locvars ),

      -- No type abstraction in data type declarations in the surface syntax:
      -- ("DataTypeDeclRHS -> [ Identifiers ] . DataTypeDeclRHS", \rhs ->
      --      let tyvars = fromASTIdSeq (get rhs 2) in
      --      case fromASTTriple (get rhs 5) of
      --        ([], [], tycondecls) -> toASTTriple ([], tyvars, tycondecls)
      --        (locvars, [], tycondecls) ->
      --          error $ "Not supported yet: types and then locations abstractions: "
      --                      ++ show tyvars ++ " " ++ show locvars
      --        (locvars, tyvars', tycondecls) ->
      --          error $ "Not supported yet: multiple type abstractions: "
      --                      ++ show tyvars' ++ " " ++ show tyvars ),


      {- TypeConDecl -}
      ("TypeConDecl -> identifier OptAtomicTypes",
        \rhs -> toASTTypeConDecl (TypeCon (getText rhs 1) (fromASTTypeSeq (get rhs 2))) ),


      {- TypeConDecls -}
      ("TypeConDecls -> TypeConDecl",
        \rhs -> toASTTypeConDeclSeq [ fromASTTypeConDecl (get rhs 1) ] ),

      ("TypeConDecls -> TypeConDecl | TypeConDecls",
        \rhs -> toASTTypeConDeclSeq $
                  fromASTTypeConDecl (get rhs 1) : fromASTTypeConDeclSeq (get rhs 3) ),


      {- Binding -}
      ("Binding -> identifier : Type = LExpr",
        \rhs -> toASTBindingDecl (
                  Binding False (getText rhs 1) (fromASTType (get rhs 3)) (fromASTExpr (get rhs 5))) ),


      {- Bindings -}
      ("Bindings -> Binding",
        \rhs -> toASTBindingDeclSeq [ fromASTBindingDecl (get rhs 1) ] ),

      ("Bindings -> Binding ; Bindings",
        \rhs -> toASTBindingDeclSeq $ fromASTBindingDecl (get rhs 1) : fromASTBindingDeclSeq (get rhs 3) ),


      {- LExpr -}
      -- No location abstractions in the surface syntax:
      -- ("LExpr -> { Identifiers } . LExpr",
      --  \rhs -> toASTExpr (singleLocAbs (LocAbs (fromASTIdSeq (get rhs 2)) (fromASTExpr (get rhs 5)))) ),

      -- No type abstractions in the surface syntax:
      -- ("LExpr -> [ Identifiers ] . LExpr",
      --   \rhs -> toASTExpr (singleTypeAbs (TypeAbs (fromASTIdSeq (get rhs 2)) (fromASTExpr (get rhs 5)))) ),

      -- [Desugar OptAtLoc]
      --   (1) OptAtLoc = @ a:
      --        \ x1 @ a ... xk @ a. expr
      --   (2) OptAtLoc = nothing:
      --        /\l. \x1 @ l ... xk @ l. expr
      
      ("LExpr -> \\ Identifiers OptAtLoc . LExpr",
        \rhs ->
          let maybeLoc = fromASTOptLocation (get rhs 3)
              
              replaceLoc x = (x, Nothing, getLocFromMaybe maybeLoc)
              
              optLocAbs Nothing  expr = LocAbs [SurfaceType.optionalLocVarName] expr
              optLocAbs (Just _) expr = expr
          in
          toASTExpr
            (optLocAbs maybeLoc
             (singleAbs
              (Abs
               (map replaceLoc ( fromASTIdSeq (get rhs 2)) )
               (fromASTExpr (get rhs 5))))) ),

      ("LExpr -> let { Bindings } LExpr end",
        \rhs -> toASTExpr (Let (fromASTBindingDeclSeq (get rhs 3)) (fromASTExpr (get rhs 5))) ),

      ("LExpr -> if Expr then LExpr else LExpr",
        \rhs -> toASTExpr (Case (fromASTExpr (get rhs 2)) Nothing
                  [ Alternative trueLit  [] (fromASTExpr (get rhs 4))
                  , Alternative falseLit [] (fromASTExpr (get rhs 6)) ]) ),

      ("LExpr -> case Expr { Alternatives }",
        \rhs -> toASTExpr (Case (fromASTExpr (get rhs 2)) Nothing (fromASTAlternativeSeq (get rhs 4))) ),

      ("LExpr -> Expr", \rhs -> get rhs 1 ),


      ("OptAtLoc -> ", \rhs -> toASTOptLocation Nothing),

      -- Todo: Location should be a constant?
      ("OptAtLoc -> @ Location", \rhs -> toASTOptLocation (Just (fromASTLocation (get rhs 2))) ),

      {- Alternatives -}
      ("Alternatives -> Alternative", \rhs -> toASTAlternativeSeq [fromASTAlternative (get rhs 1)] ),

      ("Alternatives -> Alternative ; Alternatives",
        \rhs -> toASTAlternativeSeq $ fromASTAlternative (get rhs 1) : fromASTAlternativeSeq (get rhs 3) ),


      {- Alternative -}
      ("Alternative -> identifier OptIdentifiers => LExpr",
        \rhs -> toASTAlternative $
                  (Alternative (getText rhs 1) (fromASTIdSeq (get rhs 2)) (fromASTExpr (get rhs 4))) ),

      ("Alternative -> ( OptIdentifierCommas ) => LExpr",
        \rhs -> toASTAlternative $
                  (TupleAlternative (fromASTIdSeq (get rhs 2)) (fromASTExpr (get rhs 5))) ),


      {- Expr -}
      ("Expr -> Expr Term",
        \rhs -> toASTExpr (App (fromASTExpr (get rhs 1)) Nothing (fromASTExpr (get rhs 2)) Nothing) ),

      -- No type applications in the surface syntax:
      --  Expr -> Expr [ LocFunTypes ]

      ("Expr -> Expr { Identifiers }",
        \rhs -> toASTExpr (singleLocApp (LocApp (fromASTExpr (get rhs 1)) Nothing (map locOrVar (fromASTIdSeq (get rhs 3))))) ),

      ("Expr -> Tuple", \rhs -> get rhs 1 ),

      ("Expr -> AssignExpr", \rhs -> get rhs 1 ),


      {- Tuple -}
      ("Tuple -> ( LExpr , LExprSeq )",
        \rhs -> toASTExpr (Tuple $ fromASTExpr (get rhs 2) : fromASTExprSeq (get rhs 4)) ),


      {- LExprSeq -}
      ("LExprSeq -> LExpr", \rhs -> toASTExprSeq [ fromASTExpr (get rhs 1) ] ),

      ("LExprSeq -> LExpr , LExprSeq",
        \rhs -> toASTExprSeq ( fromASTExpr (get rhs 1) : fromASTExprSeq (get rhs 3)) ),


      {- AssignExpr -}
      ("AssignExpr -> DerefExpr", \rhs -> get rhs 1 ),

      ("AssignExpr -> DerefExpr := AssignExpr",
       \rhs ->
         toASTExpr
         (App
          (App
            (Var ":=")
            Nothing
            (fromASTExpr (get rhs 1))
            Nothing )
          Nothing
          (fromASTExpr (get rhs 3))
          Nothing) ),


      {- DerefExpr -}
      -- ("DerefExpr -> LogicNot", \rhs -> get rhs 1 ),
      
      ("DerefExpr -> ! DerefExpr",
       \rhs ->
         toASTExpr
         (App
           (Var "!")
           Nothing
           (fromASTExpr (get rhs 2)) Nothing) ),

      
      ("DerefExpr -> LogicOr", \rhs -> get rhs 1 ),


      {- Expression operations -}
      ("LogicOr -> LogicOr or LogicAnd",
        \rhs -> toASTExpr (Prim OrPrimOp [] [] [fromASTExpr (get rhs 1), fromASTExpr (get rhs 3)]) ),

      ("LogicOr -> LogicAnd", \rhs -> get rhs 1),

      ("LogicAnd -> LogicAnd and CompEqNeq",
        \rhs -> toASTExpr (Prim AndPrimOp [] [] [fromASTExpr (get rhs 1), fromASTExpr (get rhs 3)]) ),

      ("LogicAnd -> CompEqNeq", \rhs -> get rhs 1),

      ("CompEqNeq -> CompEqNeq == Comp",  -- Assume EqIntPrimOp, which may change to EqBoolOp or EqStringOp later
        \rhs -> toASTExpr (Prim EqPrimOp [] [] [fromASTExpr (get rhs 1), fromASTExpr (get rhs 3)]) ),

      ("CompEqNeq -> CompEqNeq != Comp",
        \rhs -> toASTExpr (Prim NeqPrimOp [] [] [fromASTExpr (get rhs 1), fromASTExpr (get rhs 3)]) ),

      ("CompEqNeq -> Comp", \rhs -> get rhs 1 ),

      ("Comp -> Comp < ArithAddSub",
        \rhs -> toASTExpr (Prim LtPrimOp [] [] [fromASTExpr (get rhs 1), fromASTExpr (get rhs 3)]) ),

      ("Comp -> Comp <= ArithAddSub",
        \rhs -> toASTExpr (Prim LePrimOp [] [] [fromASTExpr (get rhs 1), fromASTExpr (get rhs 3)]) ),

      ("Comp -> Comp > ArithAddSub",
        \rhs -> toASTExpr (Prim GtPrimOp [] [] [fromASTExpr (get rhs 1), fromASTExpr (get rhs 3)]) ),

      ("Comp -> Comp >= ArithAddSub",
        \rhs -> toASTExpr (Prim GePrimOp [] [] [fromASTExpr (get rhs 1), fromASTExpr (get rhs 3)]) ),

      ("Comp -> ArithAddSub", \rhs -> get rhs 1 ),

      ("ArithAddSub -> ArithAddSub + ArithMulDiv",
        \rhs -> toASTExpr (Prim AddPrimOp [] [] [fromASTExpr (get rhs 1), fromASTExpr (get rhs 3)]) ),

      ("ArithAddSub -> ArithAddSub - ArithMulDiv",
        \rhs -> toASTExpr (Prim SubPrimOp [] [] [fromASTExpr (get rhs 1), fromASTExpr (get rhs 3)]) ),

      ("ArithAddSub -> ArithMulDiv", \rhs -> get rhs 1 ),

      ("ArithMulDiv -> ArithMulDiv * ArithUnary",
        \rhs -> toASTExpr (Prim MulPrimOp [] [] [fromASTExpr (get rhs 1), fromASTExpr (get rhs 3)]) ),

      ("ArithMulDiv -> ArithMulDiv / ArithUnary",
        \rhs -> toASTExpr (Prim DivPrimOp [] [] [fromASTExpr (get rhs 1), fromASTExpr (get rhs 3)]) ),

      ("ArithMulDiv -> ArithUnary", \rhs -> get rhs 1 ),

      ("ArithUnary -> - Term", \rhs -> toASTExpr (Prim NegPrimOp [] [] [fromASTExpr (get rhs 2)]) ),

      ("ArithUnary -> Term", \rhs -> get rhs 1 ),


      {- Term -}
      ("Term -> identifier", \rhs -> toASTExpr (Var (getText rhs 1)) ),

      ("Term -> integer", \rhs -> toASTExpr (Lit (IntLit (read (getText rhs 1)))) ),

      ("Term -> string", \rhs ->
          let str = read (getText rhs 1) :: String
          in  toASTExpr (Lit (StrLit str)) ),

      ("Term -> boolean", \rhs -> toASTExpr (Lit (BoolLit (read (getText rhs 1)))) ),

      ("Term -> ( )", \rhs -> toASTExpr (Lit UnitLit) ),

      ("Term -> ( LExpr )", \rhs -> get rhs 2 )
    ],

    baseDir = "./",
    actionTblFile = "action_table.txt",
    gotoTblFile = "goto_table.txt",
    grammarFile = "prod_rules.txt",
    parserSpecFile = "mygrammar.grm",
    genparserexe = "yapb-exe"
  }
