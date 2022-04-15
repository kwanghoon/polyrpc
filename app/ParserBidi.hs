module ParserBidi where

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
parserSpec :: ParserSpec Token AST IO ()
parserSpec = ParserSpec
  {
    startSymbol = "TopLevel'",

    tokenPrecAssoc = [],
    
    parserSpecList =
    [
      rule "TopLevel' -> TopLevel" ( \rhs -> return $ get rhs 1),

      {- Identifiers -}
      rule "Identifiers -> identifier" ( \rhs -> return $ toASTIdSeq [getText rhs 1] ),

      rule "Identifiers -> identifier Identifiers" (
        \rhs -> return $ toASTIdSeq (getText rhs 1 : fromASTIdSeq (get rhs 2)) ),


      {- OptIdentifiers -}
      rule "OptIdentifiers -> " ( \rhs -> return $ toASTIdSeq [] ),

      rule "OptIdentifiers -> Identifiers" ( \rhs -> return $ get rhs 1 ),


      {- IdentifierCommas -}
      rule "IdentifierCommas -> identifier" ( \rhs -> return $ toASTIdSeq [getText rhs 1] ),

      rule "IdentifierCommas -> identifier , IdentifierCommas" (
        \rhs -> return $ toASTIdSeq (getText rhs 1 : fromASTIdSeq (get rhs 3)) ),


      {- OptIdentifierCommas -}
      rule "OptIdentifierCommas -> " ( \rhs -> return $ toASTIdSeq [] ),

      rule "OptIdentifierCommas -> IdentifierCommas" ( \rhs -> return $ get rhs 1 ),


      {- Location -}
      rule "Location -> identifier" ( \rhs -> return $ toASTLocation (locOrVar (getText rhs 1)) ),


      {- Locations -}
      rule "Locations -> Identifiers" ( \rhs -> return $
        toASTLocationSeq (map locOrVar (fromASTIdSeq (get rhs 1))) ),


      {- Type -}
      rule "Type -> LocFunType" ( \rhs -> return $ get rhs 1 ),

      rule "Type -> { Identifiers } . Type" ( \rhs -> return $
        toASTType (singleLocAbsType
                            (LocAbsType (fromASTIdSeq (get rhs 2))
                                        (fromASTType (get rhs 5)))) ),

      rule "Type -> [ Identifiers ] . Type" ( \rhs -> return $
        toASTType (singleTypeAbsType (TypeAbsType
                                              (fromASTIdSeq (get rhs 2))
                                              (fromASTType (get rhs 5)))) ),


      {- LocFunType -}
      rule "LocFunType -> AppType" ( \rhs -> return $ get rhs 1),

      rule "LocFunType -> AppType locFun LocFunType" ( \rhs -> return $
          let locfun = getText rhs 2
              loc = init (init (tail locfun))  -- extract Loc from -Loc-> ( a bit hard-coded!!)
          in  toASTType (FunType
                          (fromASTType (get rhs 1))
                          (locOrVar loc)
                          (fromASTType (get rhs 3))) ),


      {- AppType -}
      rule "AppType -> AtomicType" ( \rhs -> return $ get rhs 1),

      rule "AppType -> AppType { Locations }" ( \rhs -> return $
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

      rule "AppType -> AppType [ LocFunTypes ]" ( \rhs -> return $
          let tys = fromASTTypeSeq (get rhs 3) in
          case fromASTType (get rhs 1) of
            ConType name locs [] -> toASTType (ConType name locs tys)
            ConType name locs tys' ->
              error $ "[Parser] Not supported: multiple types: " ++ name ++ " " ++ show tys' ++ " " ++ show tys
            TypeVarType name -> toASTType (ConType name [] tys) -- Now this will never happen!
            ty ->
              error $ "[Parser] Not supported yet: " ++ show ty ++ " not ConType: " ++ show tys),


      {- AtomicType -}
      rule "AtomicType -> TupleType" ( \rhs -> return $ get rhs 1 ),

      rule "AtomicType -> ( Type )" ( \rhs -> return $ get rhs 2 ),

      rule "AtomicType -> identifier" ( \rhs -> return $ toASTType (typeconOrVar (getText rhs 1)) ),


      {- TupleType -}
      rule "TupleType -> ( Type , TypeSeq )" (
        \rhs -> return $ toASTType (TupleType $
            (fromASTType (get rhs 2)) : (fromASTTypeSeq (get rhs 4))) ),


      {- TypeSeq -}
      rule "TypeSeq -> Type" ( \rhs -> return $ toASTTypeSeq [fromASTType (get rhs 1)] ),

      rule "TypeSeq -> Type , TypeSeq" (
        \rhs -> return $ toASTTypeSeq $ fromASTType (get rhs 1) : (fromASTTypeSeq (get rhs 3)) ),


      {- LocFunTypes -}
      rule "LocFunTypes -> LocFunType" ( \rhs -> return $ toASTTypeSeq [fromASTType (get rhs 1)] ),

      rule "LocFunTypes -> LocFunType LocFunTypes" (
        \rhs -> return $ toASTTypeSeq $ fromASTType (get rhs 1) : fromASTTypeSeq (get rhs 2) ),


      {- OptLocFunTypes -}
      rule "OptLocFunTypes -> " ( \rhs -> return $ toASTTypeSeq [] ),

      rule "OptLocFunTypes -> LocFunTypes" ( \rhs -> return $ get rhs 1 ),


      {- TopLevel -}
      rule "TopLevel -> Binding" (
        \rhs -> return $ toASTTopLevelDeclSeq [BindingTopLevel (setTop (fromASTBindingDecl (get rhs 1 )))] ),

      rule "TopLevel -> Binding ; TopLevel" (
        \rhs -> return $ toASTTopLevelDeclSeq
            $ BindingTopLevel (setTop (fromASTBindingDecl (get rhs 1))) : fromASTTopLevelDeclSeq (get rhs 3) ),

      rule "TopLevel -> DataTypeDecl" (
        \rhs -> return $ toASTTopLevelDeclSeq [DataTypeTopLevel (fromASTDataTypeDecl (get rhs 1))] ),

      rule "TopLevel -> DataTypeDecl ; TopLevel" (
        \rhs -> return $ toASTTopLevelDeclSeq
            $ DataTypeTopLevel (fromASTDataTypeDecl (get rhs 1)) : (fromASTTopLevelDeclSeq (get rhs 3)) ),


      {- DataTypeDecl -}
      rule "DataTypeDecl -> data identifier = DataTypeDeclRHS" ( \rhs -> return $
           let name = getText rhs 2
               (locvars,tyvars,tycondecls) = fromASTTriple (get rhs 4)
           in toASTDataTypeDecl (DataType name locvars tyvars tycondecls)),


      {- DataTypeDeclRHS -}
      rule "DataTypeDeclRHS -> TypeConDecls" ( \rhs -> return $
           toASTTriple ([], [], fromASTTypeConDeclSeq (get rhs 1)) ),

      rule "DataTypeDeclRHS -> { Identifiers } . DataTypeDeclRHS" ( \rhs -> return $
           let locvars = fromASTIdSeq (get rhs 2) in
           case fromASTTriple (get rhs 5) of
             ([], tyvars, tycondecls) -> toASTTriple (locvars, tyvars, tycondecls)
             (locvars', tyvars, tycondecls) ->
               error $ "[Parser] Not supported yet: multiple location abstractions: "
                           ++ show locvars' ++ " " ++ show locvars ),

      rule "DataTypeDeclRHS -> [ Identifiers ] . DataTypeDeclRHS" ( \rhs -> return $
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
        \rhs -> return $ toASTTypeConDecl (TypeCon (getText rhs 1) (fromASTTypeSeq (get rhs 2))) ),


      {- TypeConDecls -}
      rule "TypeConDecls -> TypeConDecl" (
        \rhs -> return $ toASTTypeConDeclSeq [ fromASTTypeConDecl (get rhs 1) ] ),

      rule "TypeConDecls -> TypeConDecl | TypeConDecls" (
        \rhs -> return $ toASTTypeConDeclSeq $
                  fromASTTypeConDecl (get rhs 1) : fromASTTypeConDeclSeq (get rhs 3) ),


      {- Binding -}
      rule "Binding -> identifier : Type = LExpr" (
        \rhs -> return $ toASTBindingDecl (
                  Binding False (getText rhs 1) (fromASTType (get rhs 3)) (fromASTExpr (get rhs 5))) ),


      {- Bindings -}
      rule "Bindings -> Binding" (
        \rhs -> return $ toASTBindingDeclSeq [ fromASTBindingDecl (get rhs 1) ] ),

      rule "Bindings -> Binding ; Bindings" (
        \rhs -> return $ toASTBindingDeclSeq $ fromASTBindingDecl (get rhs 1) : fromASTBindingDeclSeq (get rhs 3) ),


      {- LExpr -}
      rule "LExpr -> { Identifiers } . LExpr" (
        \rhs -> return $ toASTExpr (singleLocAbs (LocAbs (fromASTIdSeq (get rhs 2)) (fromASTExpr (get rhs 5)))) ),

      -- No type abstractions in the surface syntax:
      -- rule "LExpr -> [ Identifiers ] . LExpr" (
      --   \rhs -> return $ toASTExpr (singleTypeAbs (TypeAbs (fromASTIdSeq (get rhs 2)) (fromASTExpr (get rhs 5)))) ),

      rule "LExpr -> \\ IdTypeLocSeq . LExpr" (
        \rhs -> return $ toASTExpr (singleAbs (Abs (fromASTIdTypeLocSeq (get rhs 2)) (fromASTExpr (get rhs 4)))) ),

      rule "LExpr -> let { Bindings } LExpr end" (
        \rhs -> return $ toASTExpr (Let (fromASTBindingDeclSeq (get rhs 3)) (fromASTExpr (get rhs 5))) ),

      rule "LExpr -> if Expr then LExpr else LExpr" (
        \rhs -> return $ toASTExpr (Case (fromASTExpr (get rhs 2)) Nothing
                  [ Alternative trueLit  [] (fromASTExpr (get rhs 4))
                  , Alternative falseLit [] (fromASTExpr (get rhs 6)) ]) ),

      rule "LExpr -> case Expr { Alternatives }" (
        \rhs -> return $ toASTExpr (Case (fromASTExpr (get rhs 2)) Nothing (fromASTAlternativeSeq (get rhs 4))) ),

      rule "LExpr -> Expr" ( \rhs -> return $ get rhs 1 ),


      {- IdTypeLocSeq -}
      rule "IdTypeLocSeq -> IdTypeLoc" ( \rhs -> return $ toASTIdTypeLocSeq [fromASTIdTypeLoc (get rhs 1)] ),

      rule "IdTypeLocSeq -> IdTypeLoc IdTypeLocSeq" (
        \rhs -> return $ toASTIdTypeLocSeq $ fromASTIdTypeLoc (get rhs 1) : fromASTIdTypeLocSeq (get rhs 2) ),


      {- IdTypeLoc -}
      -- No type annotation to lambda bound variable in the surface syntax:
      -- rule "IdTypeLoc -> identifier : Type @ Location",
      rule "IdTypeLoc -> identifier @ Location" (
        \rhs -> return $ toASTIdTypeLoc (getText rhs 1, Nothing, fromASTLocation (get rhs 3)) ),


      {- Alternatives -}
      rule "Alternatives -> Alternative" ( \rhs -> return $ toASTAlternativeSeq [fromASTAlternative (get rhs 1)] ),

      rule "Alternatives -> Alternative ; Alternatives" (
        \rhs -> return $ toASTAlternativeSeq $ fromASTAlternative (get rhs 1) : fromASTAlternativeSeq (get rhs 3) ),


      {- Alternative -}
      rule "Alternative -> identifier OptIdentifiers => LExpr" (
        \rhs -> return $ toASTAlternative $
                  (Alternative (getText rhs 1) (fromASTIdSeq (get rhs 2)) (fromASTExpr (get rhs 4))) ),

      rule "Alternative -> ( OptIdentifierCommas ) => LExpr" (
        \rhs -> return $ toASTAlternative $
                  (TupleAlternative (fromASTIdSeq (get rhs 2)) (fromASTExpr (get rhs 5))) ),


      {- Expr -}
      rule "Expr -> Expr Term" (
        \rhs -> return $ toASTExpr (App (fromASTExpr (get rhs 1)) Nothing (fromASTExpr (get rhs 2)) Nothing) ),

      -- No type applications in the surface syntax:
      -- rule "Expr -> Expr [ LocFunTypes ]" (
      --   \rhs -> return $ toASTExpr (singleTypeApp (TypeApp (fromASTExpr (get rhs 1)) Nothing (fromASTTypeSeq (get rhs 3)))) ),

      rule "Expr -> Expr { Identifiers }" (
        \rhs -> return $ toASTExpr (singleLocApp (LocApp (fromASTExpr (get rhs 1)) Nothing (map locOrVar (fromASTIdSeq (get rhs 3))))) ),

      rule "Expr -> Tuple" ( \rhs -> return $ get rhs 1 ),

      rule "Expr -> AssignExpr" ( \rhs -> return $ get rhs 1 ),


      {- Tuple -}
      rule "Tuple -> ( LExpr , LExprSeq )" (
        \rhs -> return $ toASTExpr (Tuple $ fromASTExpr (get rhs 2) : fromASTExprSeq (get rhs 4)) ),


      {- LExprSeq -}
      rule "LExprSeq -> LExpr" ( \rhs -> return $ toASTExprSeq [ fromASTExpr (get rhs 1) ] ),

      rule "LExprSeq -> LExpr , LExprSeq" (
        \rhs -> return $ toASTExprSeq ( fromASTExpr (get rhs 1) : fromASTExprSeq (get rhs 3)) ),


      {- AssignExpr -}
      rule "AssignExpr -> DerefExpr" ( \rhs -> return $ get rhs 1 ),

      rule "AssignExpr -> DerefExpr := { Identifiers } AssignExpr" (
       \rhs -> return $
         toASTExpr
         (App
          (App
            (singleLocApp ( LocApp (Var ":=")
                                   Nothing
                                   (map locOrVar (fromASTIdSeq (get rhs 4))) ) )
            Nothing
            (fromASTExpr (get rhs 1))
            Nothing )
          Nothing
          (fromASTExpr (get rhs 6))
          Nothing) ),


      {- DerefExpr -}
      -- rule "DerefExpr -> LogicNot" ( \rhs -> return $ get rhs 1 ),
      
      rule "DerefExpr -> ! { Identifiers } DerefExpr" (
       \rhs -> return $
         toASTExpr
         (App
           (singleLocApp (LocApp (Var "!")
                                 Nothing
                                 (map locOrVar (fromASTIdSeq (get rhs 3)))))
           Nothing
           (fromASTExpr (get rhs 5)) Nothing) ),

      
      rule "DerefExpr -> LogicOr" ( \rhs -> return $ get rhs 1 ),


      {- Expression operations -}
      rule "LogicOr -> LogicOr or LogicAnd" (
        \rhs -> return $ toASTExpr (Prim OrPrimOp [] [] [fromASTExpr (get rhs 1), fromASTExpr (get rhs 3)]) ),

      rule "LogicOr -> LogicAnd" ( \rhs -> return $ get rhs 1),

      rule "LogicAnd -> LogicAnd and CompEqNeq" (
        \rhs -> return $ toASTExpr (Prim AndPrimOp [] [] [fromASTExpr (get rhs 1), fromASTExpr (get rhs 3)]) ),

      rule "LogicAnd -> CompEqNeq" ( \rhs -> return $ get rhs 1),

      rule "CompEqNeq -> CompEqNeq == Comp" (  -- Assume EqIntPrimOp, which may change to EqBoolOp or EqStringOp later
        \rhs -> return $ toASTExpr (Prim EqPrimOp [] [] [fromASTExpr (get rhs 1), fromASTExpr (get rhs 3)]) ),

      rule "CompEqNeq -> CompEqNeq != Comp" (
        \rhs -> return $ toASTExpr (Prim NeqPrimOp [] [] [fromASTExpr (get rhs 1), fromASTExpr (get rhs 3)]) ),

      rule "CompEqNeq -> Comp" ( \rhs -> return $ get rhs 1 ),

      rule "Comp -> Comp < ArithAddSub" (
        \rhs -> return $ toASTExpr (Prim LtPrimOp [] [] [fromASTExpr (get rhs 1), fromASTExpr (get rhs 3)]) ),

      rule "Comp -> Comp <= ArithAddSub" (
        \rhs -> return $ toASTExpr (Prim LePrimOp [] [] [fromASTExpr (get rhs 1), fromASTExpr (get rhs 3)]) ),

      rule "Comp -> Comp > ArithAddSub" (
        \rhs -> return $ toASTExpr (Prim GtPrimOp [] [] [fromASTExpr (get rhs 1), fromASTExpr (get rhs 3)]) ),

      rule "Comp -> Comp >= ArithAddSub" (
        \rhs -> return $ toASTExpr (Prim GePrimOp [] [] [fromASTExpr (get rhs 1), fromASTExpr (get rhs 3)]) ),

      rule "Comp -> ArithAddSub" ( \rhs -> return $ get rhs 1 ),

      rule "ArithAddSub -> ArithAddSub + ArithMulDiv" (
        \rhs -> return $ toASTExpr (Prim AddPrimOp [] [] [fromASTExpr (get rhs 1), fromASTExpr (get rhs 3)]) ),

      rule "ArithAddSub -> ArithAddSub - ArithMulDiv" (
        \rhs -> return $ toASTExpr (Prim SubPrimOp [] [] [fromASTExpr (get rhs 1), fromASTExpr (get rhs 3)]) ),

      rule "ArithAddSub -> ArithMulDiv" ( \rhs -> return $ get rhs 1 ),

      rule "ArithMulDiv -> ArithMulDiv * ArithUnary" (
        \rhs -> return $ toASTExpr (Prim MulPrimOp [] [] [fromASTExpr (get rhs 1), fromASTExpr (get rhs 3)]) ),

      rule "ArithMulDiv -> ArithMulDiv / ArithUnary" (
        \rhs -> return $ toASTExpr (Prim DivPrimOp [] [] [fromASTExpr (get rhs 1), fromASTExpr (get rhs 3)]) ),

      rule "ArithMulDiv -> ArithUnary" ( \rhs -> return $ get rhs 1 ),

      rule "ArithUnary -> - Term" ( \rhs -> return $ toASTExpr (Prim NegPrimOp [] [] [fromASTExpr (get rhs 2)]) ),

      rule "ArithUnary -> Term" ( \rhs -> return $ get rhs 1 ),


      {- Term -}
      rule "Term -> identifier" ( \rhs -> return $ toASTExpr (Var (getText rhs 1)) ),

      rule "Term -> integer" ( \rhs -> return $ toASTExpr (Lit (IntLit (read (getText rhs 1)))) ),

      rule "Term -> string" ( \rhs -> return $
          let str = read (getText rhs 1) :: String
          in  toASTExpr (Lit (StrLit str)) ),

      rule "Term -> boolean" ( \rhs -> return $ toASTExpr (Lit (BoolLit (read (getText rhs 1)))) ),

      rule "Term -> ( )" ( \rhs -> return $ toASTExpr (Lit UnitLit) ),

      rule "Term -> ( LExpr )" ( \rhs -> return $ get rhs 2 )
    ],

    synCompSpec = Nothing,
    
    baseDir = "./",
    actionTblFile = "action_table.txt",
    gotoTblFile = "goto_table.txt",
    grammarFile = "prod_rules.txt",
    parserSpecFile = "mygrammar.grm",
    genparserexe = "yapb-exe"
  }
