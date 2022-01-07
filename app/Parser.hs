module Parser where

import CommonParserUtil
import Location
import Token
import Type
import Prim
import Literal
import Expr


-- | Utility
rule prodRule action              = (prodRule, action, Nothing  )
ruleWithPrec prodRule action prec = (prodRule, action, Just prec)

-- |
parserSpec :: ParserSpec Token AST
parserSpec = ParserSpec
  {
    startSymbol = "TopLevel'",

    tokenPrecAssoc = [],
    
    parserSpecList =
    [
      rule "TopLevel' -> TopLevel" ( \rhs -> get rhs 1),

      {- Identifiers -}
      rule "Identifiers -> identifier" ( \rhs -> toASTIdSeq [getText rhs 1] ),

      rule "Identifiers -> identifier Identifiers" (
        \rhs -> toASTIdSeq (getText rhs 1 : fromASTIdSeq (get rhs 2)) ),


      {- OptIdentifiers -}
      rule "OptIdentifiers -> " ( \rhs -> toASTIdSeq [] ),

      rule "OptIdentifiers -> Identifiers" ( \rhs -> get rhs 1 ),


      {- IdentifierCommas -}
      rule "IdentifierCommas -> identifier" ( \rhs -> toASTIdSeq [getText rhs 1] ),

      rule "IdentifierCommas -> identifier , IdentifierCommas" (
        \rhs -> toASTIdSeq (getText rhs 1 : fromASTIdSeq (get rhs 3)) ),


      {- OptIdentifierCommas -}
      rule "OptIdentifierCommas -> " ( \rhs -> toASTIdSeq [] ),

      rule "OptIdentifierCommas -> IdentifierCommas" ( \rhs -> get rhs 1 ),


      {- Location -}
      rule "Location -> identifier" ( \rhs -> toASTLocation (Location (getText rhs 1)) ),


      {- Locations -}
      rule "Locations -> Identifiers" ( \rhs ->
        toASTLocationSeq (map Location (fromASTIdSeq (get rhs 1))) ),


      {- Type -}
      rule "Type -> LocFunType" ( \rhs -> get rhs 1 ),

      rule "Type -> { Identifiers } . Type" ( \rhs ->
        toASTType (singleLocAbsType
                            (LocAbsType (fromASTIdSeq (get rhs 2))
                                        (fromASTType (get rhs 5)))) ),

      rule "Type -> [ Identifiers ] . Type" ( \rhs ->
        toASTType (singleTypeAbsType (TypeAbsType
                                              (fromASTIdSeq (get rhs 2))
                                              (fromASTType (get rhs 5)))) ),


      {- LocFunType -}
      rule "LocFunType -> AppType" ( \rhs -> get rhs 1),

      rule "LocFunType -> AppType locFun LocFunType" ( \rhs ->
          let locfun = getText rhs 2
              loc = init (init (tail locfun))  -- extract Loc from -Loc-> ( a bit hard-coded!!)
          in  toASTType (FunType
                          (fromASTType (get rhs 1))
                          (Location loc)
                          (fromASTType (get rhs 3))) ),


      {- AppType -}
      rule "AppType -> AtomicType" ( \rhs -> get rhs 1),

      rule "AppType -> AppType { Locations }" ( \rhs ->
          let locs = fromASTLocationSeq (get rhs 3) in
          case fromASTType (get rhs 1) of
            ConType name [] [] -> toASTType (ConType name locs [])
            ConType name [] tys ->
              error $ "[Parser] Not supported: types and then locations: " ++ show locs ++ " " ++ show tys
            ConType name locs' tys ->
              error $ "[Parser] Not supported: multiple locations" ++ name ++ " " ++ show locs' ++ " " ++ show locs
            TypeVarType name -> toASTType (ConType name locs [])
            ty ->
              error $ "[Parser] Not supported yet: " ++ show ty ++ " not ConType: " ++ show locs),

      rule "AppType -> AppType [ LocFunTypes ]" ( \rhs ->
          let tys = fromASTTypeSeq (get rhs 3) in
          case fromASTType (get rhs 1) of
            ConType name locs [] -> toASTType (ConType name locs tys)
            ConType name locs tys' ->
              error $ "[Parser] Not supported: multiple types: " ++ name ++ " " ++ show tys' ++ " " ++ show tys
            TypeVarType name -> toASTType (ConType name [] tys)
            ty ->
              error $ "[Parser] Not supported yet: " ++ show ty ++ " not ConType: " ++ show tys),


      {- AtomicType -}
      rule "AtomicType -> TupleType" ( \rhs -> get rhs 1 ),

      rule "AtomicType -> ( Type )" ( \rhs -> get rhs 2 ),

      rule "AtomicType -> identifier" ( \rhs -> toASTType (TypeVarType (getText rhs 1)) ),


      {- TupleType -}
      rule "TupleType -> ( Type , TypeSeq )" (
        \rhs -> toASTType (TupleType $
            (fromASTType (get rhs 2)) : (fromASTTypeSeq (get rhs 4))) ),


      {- TypeSeq -}
      rule "TypeSeq -> Type" ( \rhs -> toASTTypeSeq [fromASTType (get rhs 1)] ),

      rule "TypeSeq -> Type , TypeSeq" (
        \rhs -> toASTTypeSeq $ fromASTType (get rhs 1) : (fromASTTypeSeq (get rhs 3)) ),


      {- LocFunTypes -}
      rule "LocFunTypes -> LocFunType" ( \rhs -> toASTTypeSeq [fromASTType (get rhs 1)] ),

      rule "LocFunTypes -> LocFunType LocFunTypes" (
        \rhs -> toASTTypeSeq $ fromASTType (get rhs 1) : fromASTTypeSeq (get rhs 2) ),


      {- OptLocFunTypes -}
      rule "OptLocFunTypes -> " ( \rhs -> toASTTypeSeq [] ),

      rule "OptLocFunTypes -> LocFunTypes" ( \rhs -> get rhs 1 ),


      {- TopLevel -}
      rule "TopLevel -> Binding" (
        \rhs -> toASTTopLevelDeclSeq [BindingTopLevel (setTop (fromASTBindingDecl (get rhs 1 )))] ),

      rule "TopLevel -> Binding ; TopLevel" (
        \rhs -> toASTTopLevelDeclSeq
            $ BindingTopLevel (setTop (fromASTBindingDecl (get rhs 1))) : fromASTTopLevelDeclSeq (get rhs 3) ),

      rule "TopLevel -> DataTypeDecl" (
        \rhs -> toASTTopLevelDeclSeq [DataTypeTopLevel (fromASTDataTypeDecl (get rhs 1))] ),

      rule "TopLevel -> DataTypeDecl ; TopLevel" (
        \rhs -> toASTTopLevelDeclSeq
            $ DataTypeTopLevel (fromASTDataTypeDecl (get rhs 1)) : (fromASTTopLevelDeclSeq (get rhs 3)) ),


      {- DataTypeDecl -}
      rule "DataTypeDecl -> data identifier = DataTypeDeclRHS" ( \rhs ->
           let name = getText rhs 2
               (locvars,tyvars,tycondecls) = fromASTTriple (get rhs 4)
           in toASTDataTypeDecl (DataType name locvars tyvars tycondecls)),


      {- DataTypeDeclRHS -}
      rule "DataTypeDeclRHS -> TypeConDecls" ( \rhs ->
           toASTTriple ([], [], fromASTTypeConDeclSeq (get rhs 1)) ),

      rule "DataTypeDeclRHS -> { Identifiers } . DataTypeDeclRHS" ( \rhs ->
           let locvars = fromASTIdSeq (get rhs 2) in
           case fromASTTriple (get rhs 5) of
             ([], tyvars, tycondecls) -> toASTTriple (locvars, tyvars, tycondecls)
             (locvars', tyvars, tycondecls) ->
               error $ "[Parser] Not supported yet: multiple location abstractions: "
                           ++ show locvars' ++ " " ++ show locvars ),

      rule "DataTypeDeclRHS -> [ Identifiers ] . DataTypeDeclRHS" ( \rhs ->
           let tyvars = fromASTIdSeq (get rhs 2) in
           case fromASTTriple (get rhs 5) of
             ([], [], tycondecls) -> toASTTriple ([], tyvars, tycondecls)
             (locvars, [], tycondecls) ->
               error $ "Not supported yet: types and then locations abstractions: "
                           ++ show tyvars ++ " " ++ show locvars
             (locvars, tyvars', tycondecls) ->
               error $ "Not supported yet: multiple type abstractions: "
                           ++ show tyvars' ++ " " ++ show tyvars ),


      {- TypeConDecl -}
      rule "TypeConDecl -> identifier OptLocFunTypes" (
        \rhs -> toASTTypeConDecl (TypeCon (getText rhs 1) (fromASTTypeSeq (get rhs 2))) ),


      {- TypeConDecls -}
      rule "TypeConDecls -> TypeConDecl" (
        \rhs -> toASTTypeConDeclSeq [ fromASTTypeConDecl (get rhs 1) ] ),

      rule "TypeConDecls -> TypeConDecl | TypeConDecls" (
        \rhs -> toASTTypeConDeclSeq $
                  fromASTTypeConDecl (get rhs 1) : fromASTTypeConDeclSeq (get rhs 3) ),


      {- Binding -}
      rule "Binding -> identifier : Type = LExpr" (
        \rhs -> toASTBindingDecl (
                  Binding False (getText rhs 1) (fromASTType (get rhs 3)) (fromASTExpr (get rhs 5))) ),


      {- Bindings -}
      rule "Bindings -> Binding" (
        \rhs -> toASTBindingDeclSeq [ fromASTBindingDecl (get rhs 1) ] ),

      rule "Bindings -> Binding ; Bindings" (
        \rhs -> toASTBindingDeclSeq $ fromASTBindingDecl (get rhs 1) : fromASTBindingDeclSeq (get rhs 3) ),


      {- LExpr -}
      rule "LExpr -> { Identifiers } . LExpr" (
        \rhs -> toASTExpr (singleLocAbs (LocAbs (fromASTIdSeq (get rhs 2)) (fromASTExpr (get rhs 5)))) ),

      rule "LExpr -> [ Identifiers ] . LExpr" (
        \rhs -> toASTExpr (singleTypeAbs (TypeAbs (fromASTIdSeq (get rhs 2)) (fromASTExpr (get rhs 5)))) ),

      rule "LExpr -> \\ IdTypeLocSeq . LExpr" (
        \rhs -> toASTExpr (singleAbs (Abs (fromASTIdTypeLocSeq (get rhs 2)) (fromASTExpr (get rhs 4)))) ),

      rule "LExpr -> let { Bindings } LExpr end" (
        \rhs -> toASTExpr (Let (fromASTBindingDeclSeq (get rhs 3)) (fromASTExpr (get rhs 5))) ),

      rule "LExpr -> if Expr then LExpr else LExpr" (
        \rhs -> toASTExpr (Case (fromASTExpr (get rhs 2)) Nothing
                  [ Alternative trueLit  [] (fromASTExpr (get rhs 4))
                  , Alternative falseLit [] (fromASTExpr (get rhs 6)) ]) ),

      rule "LExpr -> case Expr { Alternatives }" (
        \rhs -> toASTExpr (Case (fromASTExpr (get rhs 2)) Nothing (fromASTAlternativeSeq (get rhs 4))) ),

      rule "LExpr -> Expr" ( \rhs -> get rhs 1 ),


      {- IdTypeLocSeq -}
      rule "IdTypeLocSeq -> IdTypeLoc" ( \rhs -> toASTIdTypeLocSeq [fromASTIdTypeLoc (get rhs 1)] ),

      rule "IdTypeLocSeq -> IdTypeLoc IdTypeLocSeq" (
        \rhs -> toASTIdTypeLocSeq $ fromASTIdTypeLoc (get rhs 1) : fromASTIdTypeLocSeq (get rhs 2) ),


      {- IdTypeLoc -}
      rule "IdTypeLoc -> identifier : Type @ Location" (
        \rhs -> toASTIdTypeLoc (getText rhs 1, Just (fromASTType (get rhs 3)), fromASTLocation (get rhs 5)) ),


      {- Alternatives -}
      rule "Alternatives -> Alternative" ( \rhs -> toASTAlternativeSeq [fromASTAlternative (get rhs 1)] ),

      rule "Alternatives -> Alternative ; Alternatives" (
        \rhs -> toASTAlternativeSeq $ fromASTAlternative (get rhs 1) : fromASTAlternativeSeq (get rhs 3) ),


      {- Alternative -}
      rule "Alternative -> identifier OptIdentifiers => LExpr" (
        \rhs -> toASTAlternative $
                  (Alternative (getText rhs 1) (fromASTIdSeq (get rhs 2)) (fromASTExpr (get rhs 4))) ),

      rule "Alternative -> ( OptIdentifierCommas ) => LExpr" (
        \rhs -> toASTAlternative $
                  (TupleAlternative (fromASTIdSeq (get rhs 2)) (fromASTExpr (get rhs 5))) ),


      {- Expr -}
      rule "Expr -> Expr Term" (
        \rhs -> toASTExpr (App (fromASTExpr (get rhs 1)) Nothing (fromASTExpr (get rhs 2)) Nothing) ),

      rule "Expr -> Expr [ LocFunTypes ]" (
        \rhs -> toASTExpr (singleTypeApp (TypeApp (fromASTExpr (get rhs 1)) Nothing (fromASTTypeSeq (get rhs 3)))) ),

      rule "Expr -> Expr { Identifiers }" (
        \rhs -> toASTExpr (singleLocApp (LocApp (fromASTExpr (get rhs 1)) Nothing (map Location (fromASTIdSeq (get rhs 3))))) ),

      rule "Expr -> Tuple" ( \rhs -> get rhs 1 ),

      rule "Expr -> AssignExpr" ( \rhs -> get rhs 1 ),


      {- Tuple -}
      rule "Tuple -> ( LExpr , LExprSeq )" (
        \rhs -> toASTExpr (Tuple $ fromASTExpr (get rhs 2) : fromASTExprSeq (get rhs 4)) ),


      {- LExprSeq -}
      rule "LExprSeq -> LExpr" ( \rhs -> toASTExprSeq [ fromASTExpr (get rhs 1) ] ),

      rule "LExprSeq -> LExpr , LExprSeq" (
        \rhs -> toASTExprSeq ( fromASTExpr (get rhs 1) : fromASTExprSeq (get rhs 3)) ),


      {- AssignExpr -}
      rule "AssignExpr -> DerefExpr" ( \rhs -> get rhs 1 ),

      rule "AssignExpr -> DerefExpr := { Identifiers } [ LocFunTypes ] AssignExpr" (
       \rhs ->
         toASTExpr
         (App
          (App
           (singleTypeApp (TypeApp
            (singleLocApp ( LocApp (Var ":=")
                                   Nothing
                                   (map Location (fromASTIdSeq (get rhs 4))) ) )
            Nothing
            (fromASTTypeSeq (get rhs 7)) ) )
           Nothing
           (fromASTExpr (get rhs 1))
           Nothing )
          Nothing
          (fromASTExpr (get rhs 9))
          Nothing) ),


      {- DerefExpr -}
      rule "DerefExpr -> LogicNot" ( \rhs -> get rhs 1 ),

      rule "DerefExpr -> ! { Identifiers } [ LocFunTypes ] DerefExpr" (
       \rhs ->
         toASTExpr
         (App
          (singleTypeApp (TypeApp
           (singleLocApp (LocApp (Var "!")
                                 Nothing
                                 (map Location (fromASTIdSeq (get rhs 3)))))
           Nothing
           (fromASTTypeSeq (get rhs 6)) ))
          Nothing
          (fromASTExpr (get rhs 8)) Nothing) ),

      rule "DerefExpr -> LogicOr" ( \rhs -> get rhs 1 ),


      {- Expression operations -}
      rule "LogicOr -> LogicOr or LogicAnd" (
        \rhs -> toASTExpr (Prim OrPrimOp [] [] [fromASTExpr (get rhs 1), fromASTExpr (get rhs 3)]) ),

      rule "LogicOr -> LogicAnd" ( \rhs -> get rhs 1),

      rule "LogicAnd -> LogicAnd and CompEqNeq" (
        \rhs -> toASTExpr (Prim AndPrimOp [] [] [fromASTExpr (get rhs 1), fromASTExpr (get rhs 3)]) ),

      rule "LogicAnd -> CompEqNeq" ( \rhs -> get rhs 1),

      rule "CompEqNeq -> CompEqNeq == Comp" (  -- Assume EqIntPrimOp, which may change to EqBoolOp or EqStringOp later
        \rhs -> toASTExpr (Prim EqIntPrimOp [] [] [fromASTExpr (get rhs 1), fromASTExpr (get rhs 3)]) ),

      rule "CompEqNeq -> CompEqNeq != Comp" (
        \rhs -> toASTExpr (Prim NeqPrimOp [] [] [fromASTExpr (get rhs 1), fromASTExpr (get rhs 3)]) ),

      rule "CompEqNeq -> Comp" ( \rhs -> get rhs 1 ),

      rule "Comp -> Comp < ArithAddSub" (
        \rhs -> toASTExpr (Prim LtPrimOp [] [] [fromASTExpr (get rhs 1), fromASTExpr (get rhs 3)]) ),

      rule "Comp -> Comp <= ArithAddSub" (
        \rhs -> toASTExpr (Prim LePrimOp [] [] [fromASTExpr (get rhs 1), fromASTExpr (get rhs 3)]) ),

      rule "Comp -> Comp > ArithAddSub" (
        \rhs -> toASTExpr (Prim GtPrimOp [] [] [fromASTExpr (get rhs 1), fromASTExpr (get rhs 3)]) ),

      rule "Comp -> Comp >= ArithAddSub" (
        \rhs -> toASTExpr (Prim GePrimOp [] [] [fromASTExpr (get rhs 1), fromASTExpr (get rhs 3)]) ),

      rule "Comp -> ArithAddSub" ( \rhs -> get rhs 1 ),

      rule "ArithAddSub -> ArithAddSub + ArithMulDiv" (
        \rhs -> toASTExpr (Prim AddPrimOp [] [] [fromASTExpr (get rhs 1), fromASTExpr (get rhs 3)]) ),

      rule "ArithAddSub -> ArithAddSub - ArithMulDiv" (
        \rhs -> toASTExpr (Prim SubPrimOp [] [] [fromASTExpr (get rhs 1), fromASTExpr (get rhs 3)]) ),

      rule "ArithAddSub -> ArithMulDiv" ( \rhs -> get rhs 1 ),

      rule "ArithMulDiv -> ArithMulDiv * ArithUnary" (
        \rhs -> toASTExpr (Prim MulPrimOp [] [] [fromASTExpr (get rhs 1), fromASTExpr (get rhs 3)]) ),

      rule "ArithMulDiv -> ArithMulDiv / ArithUnary" (
        \rhs -> toASTExpr (Prim DivPrimOp [] [] [fromASTExpr (get rhs 1), fromASTExpr (get rhs 3)]) ),

      rule "ArithMulDiv -> ArithUnary" ( \rhs -> get rhs 1 ),

      rule "ArithUnary -> - Term" ( \rhs -> toASTExpr (Prim NegPrimOp [] [] [fromASTExpr (get rhs 2)]) ),

      rule "ArithUnary -> Term" ( \rhs -> get rhs 1 ),


      {- Term -}
      rule "Term -> identifier" ( \rhs -> toASTExpr (Var (getText rhs 1)) ),

      rule "Term -> integer" ( \rhs -> toASTExpr (Lit (IntLit (read (getText rhs 1)))) ),

      rule "Term -> string" ( \rhs ->
          let str = read (getText rhs 1) :: String
          in  toASTExpr (Lit (StrLit str)) ),

      rule "Term -> boolean" ( \rhs -> toASTExpr (Lit (BoolLit (read (getText rhs 1)))) ),

      rule "Term -> ( )" ( \rhs -> toASTExpr (Lit UnitLit) ),

      rule "Term -> ( LExpr )" ( \rhs -> get rhs 2 )
    ],

    baseDir = "./",
    actionTblFile = "action_table.txt",
    gotoTblFile = "goto_table.txt",
    grammarFile = "prod_rules.txt",
    parserSpecFile = "mygrammar.grm",
    genparserexe = "yapb-exe"
  }
