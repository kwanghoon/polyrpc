module ParserBidiLinks where

-- | A parsimonius approach to location polymorphism

--   (1) {Loc} A -> B  vs.  A -Loc-> B  ({Loc} A will actually replace all locations deep inside A)
--   (2) \{Loc} x1 ... xk . e  vs. \x1 @ Loc ... xk @ Loc . e
--   (3) data D {l1 ... li} a1 ... ak = Con ty1 ... tyn | ...
--       vs. data D = {l1 ... li} [a1 ... ak] Con ty1 ... tyn | ...
--   (4) forall a1 ... ak ty  vs.  [a1 ... ak] ty
--   (5) ty  vs {l1 ... li} ty
--   (6) ! expr  vs. ! {Loc} expr
--   (7) var := expr  vs. var := {Loc} expr

--   Design consideration

--    - Programmers have only to write client and server, not location
--      variables.
--
--    - No explicit location abstractions in function declarations
--      but in datatype declarations.
--
--    - At most one location abstraction in function declarations
--      but more can be in datatype declarations.
--
--    - Basically, location abstractions are assumed to be in the
--      prenex form. No higher-ranked location abstraction types.

import CommonParserUtil
import Location
import Token
import Type
import Prim
import Literal
import Expr
import Surface

import Data.Set(delete, toList)

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
      rule "TopLevel' -> TopLevel" (\rhs -> return $ get rhs 1),

      {- Identifiers -}
      rule "Identifiers -> identifier" (\rhs -> return $ toASTIdSeq [getText rhs 1] ),

      rule "Identifiers -> identifier Identifiers"
        (\rhs -> return $ toASTIdSeq (getText rhs 1 : fromASTIdSeq (get rhs 2)) ),


      {- OptIdentifiers -}
      rule "OptIdentifiers -> " (\rhs -> return $ toASTIdSeq [] ),

      rule "OptIdentifiers -> Identifiers" (\rhs -> return $ get rhs 1 ),


      {- IdentifierCommas -}
      rule "IdentifierCommas -> identifier" (\rhs -> return $ toASTIdSeq [getText rhs 1] ),

      rule "IdentifierCommas -> identifier , IdentifierCommas"
        (\rhs -> return $ toASTIdSeq (getText rhs 1 : fromASTIdSeq (get rhs 3)) ),


      {- OptIdentifierCommas -}
      rule "OptIdentifierCommas -> " (\rhs -> return $ toASTIdSeq [] ),

      rule "OptIdentifierCommas -> IdentifierCommas"  (\rhs -> return $ get rhs 1 ),


      {- Location -}
      rule "Location -> identifier" (\rhs -> return $ toASTLocation (locOrVar (getText rhs 1)) ),


      {- Locations -}
      rule "Locations -> Identifiers" (\rhs -> return $
        toASTLocationSeq (map locOrVar (fromASTIdSeq (get rhs 1))) ),


      {- Type -}
      rule "Type -> LocatedFunType" (\rhs -> return $ get rhs 1 ),

      rule "Type -> { Identifiers } . Type" (\rhs -> return $
        toASTType (singleLocAbsType
                            (LocAbsType (fromASTIdSeq (get rhs 2))
                                        (fromASTType (get rhs 5)))) ),

      -- The syntax of abstraction types is changed:
      --  Type -> [ Identifiers ] . Type
      rule "Type -> forall Identifiers . Type" (\rhs -> return $
        toASTType (singleTypeAbsType (TypeAbsType
                                              (fromASTIdSeq (get rhs 2))
                                              (fromASTType (get rhs 4)))) ),

      {- LocatedFunType -}
      rule "LocatedFunType -> FunType" (\rhs -> return $ get rhs 1),

      rule "LocatedFunType -> Location : FunType" (\rhs -> return $
          let loc = fromASTLocation (get rhs 1)
              funTy = fromASTType (get rhs 3)
          in  toASTType (annotateLocOnNoName (Just loc) funTy)
       ),
      
      {- FunType -}
      rule "FunType -> AppType" (\rhs -> return $ get rhs 1),

      rule "FunType -> AppType -> FunType" (\rhs -> return $
          let locName = Surface.noLocName
          in  toASTType (FunType (fromASTType (get rhs 1)) (locOrVar locName) (fromASTType (get rhs 3))) ),

      rule "FunType -> AppType locFun FunType" (\rhs -> return $
          let locfun = getText rhs 2
              locName = init (init (tail locfun))  -- extract Loc from -Loc-> ( a bit hard-coded!!)
          in  toASTType (FunType
                          (fromASTType (get rhs 1))
                          (locOrVar locName)
                          (fromASTType (get rhs 3))) ),

      {- AppType -}
      rule "AppType -> AtomicType" (\rhs -> return $ get rhs 1),

      rule "AppType -> AppType { Locations }" (\rhs -> return $
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
      rule "AppType -> AppType AtomicType" (\rhs -> return $
          let ty = fromASTType (get rhs 2) in
          case fromASTType (get rhs 1) of
            ConType name locs tys -> toASTType (ConType name locs (tys ++ [ty]))
            -- ConType name locs tys' ->
            --   error $ "[Parser] Not supported: multiple types: " ++ name ++ " " ++ show tys' ++ " " ++ show tys
            TypeVarType name -> toASTType (ConType name [] [ty]) -- Now this will never happen!
            ty0 ->
              error $ "[Parser] Not supported yet: " ++ show ty0 ++ " not ConType: " ++ show ty),

      {- OptAtomicTypes -}
      rule "OptAtomicTypes -> " (\rhs -> return $ toASTTypeSeq [] ),

      rule "OptAtomicTypes -> AtomicTypes" (\rhs -> return $ get rhs 1 ),
      
      {- AtomicTypes -}
      rule "AtomicTypes -> AtomicType" (\rhs -> return $ toASTTypeSeq [fromASTType (get rhs 1)] ),

      rule "AtomicTypes -> AtomicType AtomicTypes"
        (\rhs -> return $ toASTTypeSeq $ fromASTType (get rhs 1) : fromASTTypeSeq (get rhs 2) ),
      
      {- AtomicType -}
      rule "AtomicType -> TupleType" (\rhs -> return $ get rhs 1 ),

      rule "AtomicType -> ( Type )" (\rhs -> return $ get rhs 2 ),

      rule "AtomicType -> identifier" (\rhs -> return $ toASTType (typeconOrVar (getText rhs 1)) ),

      
      {- TupleType -}
      rule "TupleType -> ( )" (\rhs -> return $ toASTType (TupleType [] )),
      
      rule "TupleType -> ( Type , TypeSeq )"
        (\rhs -> return $ toASTType (TupleType $
            (fromASTType (get rhs 2)) : (fromASTTypeSeq (get rhs 4))) ),


      {- TypeSeq -}
      rule "TypeSeq -> Type" (\rhs -> return $ toASTTypeSeq [fromASTType (get rhs 1)] ),

      rule "TypeSeq -> Type , TypeSeq"
        (\rhs -> return $ toASTTypeSeq $ fromASTType (get rhs 1) : (fromASTTypeSeq (get rhs 3)) ),


      {- FunTypes -}
      -- ("FunTypes -> FunType", \rhs -> return $ toASTTypeSeq [fromASTType (get rhs 1)] ),

      -- ("FunTypes -> FunType FunTypes",
      --   \rhs -> return $ toASTTypeSeq $ fromASTType (get rhs 1) : fromASTTypeSeq (get rhs 2) ),


      {- OptType -}
      -- ("OptType -> ", \rhs -> return $ Nothing ),

      -- ("OptType -> Type", \rhs -> return $ Just $ get rhs 1 ),


      {- TopLevel -}
      rule "TopLevel -> Binding"
        (\rhs -> return $ toASTTopLevelDeclSeq [BindingTopLevel (setTop (fromASTBindingDecl (get rhs 1 )))] ),

      rule "TopLevel -> Binding ; TopLevel"
        (\rhs -> return $ toASTTopLevelDeclSeq
            $ BindingTopLevel (setTop (fromASTBindingDecl (get rhs 1))) : fromASTTopLevelDeclSeq (get rhs 3) ),

      rule "TopLevel -> DataTypeDecl"
        (\rhs -> return $ toASTTopLevelDeclSeq [DataTypeTopLevel (fromASTDataTypeDecl (get rhs 1))] ),

      rule "TopLevel -> DataTypeDecl ; TopLevel"
        (\rhs -> return $ toASTTopLevelDeclSeq
            $ DataTypeTopLevel (fromASTDataTypeDecl (get rhs 1)) : (fromASTTopLevelDeclSeq (get rhs 3)) ),


      {- DataTypeDecl -}
      rule "DataTypeDecl -> data identifier { Identifiers } OptIdentifiers = DataTypeDeclRHS" (\rhs -> return $
           let name = getText rhs 2
               locvars = fromASTIdSeq (get rhs 4)
               tyvars  = fromASTIdSeq (get rhs 6)
               (_,_,tycondecls) = fromASTTriple (get rhs 8)
           in toASTDataTypeDecl (DataType name locvars tyvars tycondecls)),

      rule "DataTypeDecl -> data identifier OptIdentifiers = DataTypeDeclRHS" (\rhs -> return $
           let name = getText rhs 2
               locvars = []
               tyvars  = fromASTIdSeq (get rhs 3)
               (_,_,tycondecls) = fromASTTriple (get rhs 5)
           in toASTDataTypeDecl (DataType name locvars tyvars tycondecls)),

      {- DataTypeDeclRHS -}
      -- Leave this later for investigating using GADT in the polymorphic RPC calculus!!
      rule "DataTypeDeclRHS -> TypeConDecls" (\rhs -> return $
           toASTTriple ([], [], fromASTTypeConDeclSeq (get rhs 1)) ),

      -- No location abstraction in data type declarations in the surface syntax:
      -- ("DataTypeDeclRHS -> { Identifiers } . DataTypeDeclRHS", \rhs -> return $
      --      let locvars = fromASTIdSeq (get rhs 2) in
      --      case fromASTTriple (get rhs 5) of
      --        ([], tyvars, tycondecls) -> toASTTriple (locvars, tyvars, tycondecls)
      --        (locvars', tyvars, tycondecls) ->
      --          error $ "[Parser] Not supported yet: multiple location abstractions: "
      --                      ++ show locvars' ++ " " ++ show locvars ),

      -- No type abstraction in data type declarations in the surface syntax:
      -- ("DataTypeDeclRHS -> [ Identifiers ] . DataTypeDeclRHS", \rhs -> return $
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
      rule "TypeConDecl -> identifier OptAtomicTypes"
        (\rhs -> return $ toASTTypeConDecl (TypeCon (getText rhs 1) (fromASTTypeSeq (get rhs 2))) ),


      {- TypeConDecls -}
      rule "TypeConDecls -> TypeConDecl"
        (\rhs -> return $ toASTTypeConDeclSeq [ fromASTTypeConDecl (get rhs 1) ] ),

      rule "TypeConDecls -> TypeConDecl | TypeConDecls"
        (\rhs -> return $ toASTTypeConDeclSeq $
                  fromASTTypeConDecl (get rhs 1) : fromASTTypeConDeclSeq (get rhs 3) ),


      {- Binding -}
      -- Like let-polymorphism, location variables are generalized for each binding
      
      rule "Binding -> identifier : Type = LExpr"  -- Todo: OptType
        (\rhs -> return $
          case fromASTType $ get rhs 3 of
            ty -> 
              let lexpr = fromASTExpr (get rhs 5)

                  locAbsTy = if isTyfromSingleWorld ty && isAbs lexpr
                    then case lexpr of
                           Abs ((_,_,loc):_) _ ->
                             case loc of
                               Location name -> annotateLoc (Just loc) ty
                               LocVar name ->
                                 -- assert (name == noLocName)
                                 LocAbsType [defaultLocVarName]
                                   (annotateLoc (Just (LocVar defaultLocVarName)) ty)

                    else ty

              in
              toASTBindingDecl (Binding False (getText rhs 1) locAbsTy lexpr)),


      {- Bindings -}
      rule "Bindings -> Binding"
        (\rhs -> return $ toASTBindingDeclSeq [ fromASTBindingDecl (get rhs 1) ] ),

      rule "Bindings -> Binding ; Bindings"
        (\rhs -> return $ toASTBindingDeclSeq $ fromASTBindingDecl (get rhs 1) : fromASTBindingDeclSeq (get rhs 3) ),


      {- LExpr -}
      -- No location abstractions in the surface syntax:
      -- ("LExpr -> { Identifiers } . LExpr",
      --  \rhs -> return $ toASTExpr (singleLocAbs (LocAbs (fromASTIdSeq (get rhs 2)) (fromASTExpr (get rhs 5)))) ),

      -- No type abstractions in the surface syntax:
      -- ("LExpr -> [ Identifiers ] . LExpr",
      --   \rhs -> return $ toASTExpr (singleTypeAbs (TypeAbs (fromASTIdSeq (get rhs 2)) (fromASTExpr (get rhs 5)))) ),

      -- [Desugar OptAtLoc]
      --   (1) OptAtLoc = {a}:
      --        \ x1 @ a ... xk @ a. expr
      --   (2) OptAtLoc =    :
      --        \x1 @ $empty ... xk @ $empty. expr    At parsing stage, $empty is introduced.
      --        \x1 @ ^l1 ... xk @ ^lk. expr          Later, $empty will be replaced by ^l
      --                                              a unification variable by a type check proc.

      rule "LExpr -> \\ Identifiers . LExpr"
        (\rhs -> return $
          let maybeLoc = Nothing
              
              replaceLoc x = (x, Nothing, Surface.getLocFromMaybe maybeLoc)
              
              -- optLocAbs Nothing  expr = LocAbs [Surface.defaultLocVarName] expr
              -- optLocAbs (Just _) expr = expr
          in
          toASTExpr
            -- (optLocAbs maybeLoc
             (singleAbs
              (Abs
               (map replaceLoc ( fromASTIdSeq (get rhs 2)) )
               (fromASTExpr (get rhs 4)))) {- ) -} ),
      
      rule "LExpr -> \\ Location : Identifiers . LExpr"
        (\rhs -> return $
          let maybeLoc = Just (fromASTLocation (get rhs 2))
              
              replaceLoc x = (x, Nothing, Surface.getLocFromMaybe maybeLoc)
              
              -- optLocAbs Nothing  expr = LocAbs [Surface.defaultLocVarName] expr
              -- optLocAbs (Just _) expr = expr
          in
          toASTExpr
            -- (optLocAbs maybeLoc
             (singleAbs
              (Abs
               (map replaceLoc ( fromASTIdSeq (get rhs 4)) )
               (fromASTExpr (get rhs 6)))) {- ) -} ),

      rule "LExpr -> let { Bindings } LExpr end"
        (\rhs -> return $ toASTExpr (Let (fromASTBindingDeclSeq (get rhs 3)) (fromASTExpr (get rhs 5))) ),

      rule "LExpr -> if Expr then LExpr else LExpr"
        (\rhs -> return $ toASTExpr (Case (fromASTExpr (get rhs 2)) Nothing
                  [ Alternative trueLit  [] (fromASTExpr (get rhs 4))
                  , Alternative falseLit [] (fromASTExpr (get rhs 6)) ]) ),

      rule "LExpr -> case Expr { Alternatives }"
        (\rhs -> return $ toASTExpr (Case (fromASTExpr (get rhs 2)) Nothing (fromASTAlternativeSeq (get rhs 4))) ),

      rule "LExpr -> Expr" (\rhs -> return $ get rhs 1 ),


      rule "OptAtLoc -> " (\rhs -> return $ toASTOptLocation Nothing),

      rule "OptAtLoc -> Location :" (\rhs -> return $ toASTOptLocation (Just (fromASTLocation (get rhs 2))) ),

      {- Alternatives -}
      rule "Alternatives -> Alternative" (\rhs -> return $ toASTAlternativeSeq [fromASTAlternative (get rhs 1)] ),

      rule "Alternatives -> Alternative ; Alternatives"
        (\rhs -> return $ toASTAlternativeSeq $ fromASTAlternative (get rhs 1) : fromASTAlternativeSeq (get rhs 3) ),


      {- Alternative -}
      rule "Alternative -> identifier OptIdentifiers => LExpr"
        (\rhs -> return $ toASTAlternative $
                  (Alternative (getText rhs 1) (fromASTIdSeq (get rhs 2)) (fromASTExpr (get rhs 4))) ),

      rule "Alternative -> ( OptIdentifierCommas ) => LExpr"
        (\rhs -> return $ toASTAlternative $
                  (TupleAlternative (fromASTIdSeq (get rhs 2)) (fromASTExpr (get rhs 5))) ),


      {- Expr -}
      rule "Expr -> Expr Term"
        (\rhs -> return $ toASTExpr (App (fromASTExpr (get rhs 1)) Nothing (fromASTExpr (get rhs 2)) Nothing) ),

      -- No type applications in the surface syntax:
      --  Expr -> Expr [ LocFunTypes ]

      rule "Expr -> Expr { Identifiers }"
        (\rhs -> return $ toASTExpr (singleLocApp (LocApp (fromASTExpr (get rhs 1)) Nothing (map locOrVar (fromASTIdSeq (get rhs 3))))) ),

      rule "Expr -> Tuple" (\rhs -> return $ get rhs 1 ),

      rule "Expr -> AssignExpr" (\rhs -> return $ get rhs 1 ),


      {- Tuple -}
      rule "Tuple -> ( LExpr , LExprSeq )"
        (\rhs -> return $ toASTExpr (Tuple $ fromASTExpr (get rhs 2) : fromASTExprSeq (get rhs 4)) ),


      {- LExprSeq -}
      rule "LExprSeq -> LExpr" (\rhs -> return $ toASTExprSeq [ fromASTExpr (get rhs 1) ] ),

      rule "LExprSeq -> LExpr , LExprSeq"
        (\rhs -> return $ toASTExprSeq ( fromASTExpr (get rhs 1) : fromASTExprSeq (get rhs 3)) ),


      {- AssignExpr -}
      rule "AssignExpr -> DerefExpr" (\rhs -> return $ get rhs 1 ),

      rule "AssignExpr -> DerefExpr := AssignExpr"
       (\rhs -> return $
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
      -- ("DerefExpr -> LogicNot", \rhs -> return $ get rhs 1 ),
      
      rule "DerefExpr -> ! DerefExpr"
       (\rhs -> return $
         toASTExpr
         (App
           (Var "!")
           Nothing
           (fromASTExpr (get rhs 2)) Nothing) ),

      
      rule "DerefExpr -> LogicOr" (\rhs -> return $ get rhs 1 ),


      {- Expression operations -}
      rule "LogicOr -> LogicOr or LogicAnd"
        (\rhs -> return $ toASTExpr (Prim OrPrimOp [] [] [fromASTExpr (get rhs 1), fromASTExpr (get rhs 3)]) ),

      rule "LogicOr -> LogicAnd" (\rhs -> return $ get rhs 1),

      rule "LogicAnd -> LogicAnd and CompEqNeq"
        (\rhs -> return $ toASTExpr (Prim AndPrimOp [] [] [fromASTExpr (get rhs 1), fromASTExpr (get rhs 3)]) ),

      rule "LogicAnd -> CompEqNeq" (\rhs -> return $ get rhs 1),

      rule "CompEqNeq -> CompEqNeq == Comp"  -- Assume EqIntPrimOp, which may change to EqBoolOp or EqStringOp later
        (\rhs -> return $ toASTExpr (Prim EqPrimOp [] [] [fromASTExpr (get rhs 1), fromASTExpr (get rhs 3)]) ),

      rule "CompEqNeq -> CompEqNeq != Comp"
        (\rhs -> return $ toASTExpr (Prim NeqPrimOp [] [] [fromASTExpr (get rhs 1), fromASTExpr (get rhs 3)]) ),

      rule "CompEqNeq -> Comp" (\rhs -> return $ get rhs 1 ),

      rule "Comp -> Comp < ArithAddSub"
        (\rhs -> return $ toASTExpr (Prim LtPrimOp [] [] [fromASTExpr (get rhs 1), fromASTExpr (get rhs 3)]) ),

      rule "Comp -> Comp <= ArithAddSub"
        (\rhs -> return $ toASTExpr (Prim LePrimOp [] [] [fromASTExpr (get rhs 1), fromASTExpr (get rhs 3)]) ),

      rule "Comp -> Comp > ArithAddSub"
        (\rhs -> return $ toASTExpr (Prim GtPrimOp [] [] [fromASTExpr (get rhs 1), fromASTExpr (get rhs 3)]) ),

      rule "Comp -> Comp >= ArithAddSub"
        (\rhs -> return $ toASTExpr (Prim GePrimOp [] [] [fromASTExpr (get rhs 1), fromASTExpr (get rhs 3)]) ),

      rule "Comp -> ArithAddSub" (\rhs -> return $ get rhs 1 ),

      rule "ArithAddSub -> ArithAddSub + ArithMulDiv"  -- Q: ArithMulDiv -> ... ???
        (\rhs -> return $ toASTExpr (Prim AddPrimOp [] [] [fromASTExpr (get rhs 1), fromASTExpr (get rhs 3)]) ),

      rule "ArithAddSub -> ArithAddSub - ArithMulDiv"
        (\rhs -> return $ toASTExpr (Prim SubPrimOp [] [] [fromASTExpr (get rhs 1), fromASTExpr (get rhs 3)]) ),

      rule "ArithAddSub -> ArithMulDiv" (\rhs -> return $ get rhs 1 ),

      rule "ArithMulDiv -> ArithMulDiv * ArithUnary"
        (\rhs -> return $ toASTExpr (Prim MulPrimOp [] [] [fromASTExpr (get rhs 1), fromASTExpr (get rhs 3)]) ),

      rule "ArithMulDiv -> ArithMulDiv / ArithUnary"
        (\rhs -> return $ toASTExpr (Prim DivPrimOp [] [] [fromASTExpr (get rhs 1), fromASTExpr (get rhs 3)]) ),

      rule "ArithMulDiv -> ArithUnary" (\rhs -> return $ get rhs 1 ),

      rule "ArithUnary -> - Term" (\rhs -> return $ toASTExpr (Prim NegPrimOp [] [] [fromASTExpr (get rhs 2)]) ),

      rule "ArithUnary -> Term" (\rhs -> return $ get rhs 1 ),


      {- Term -}
      rule "Term -> identifier" (\rhs -> return $ toASTExpr (Var (getText rhs 1)) ),

      rule "Term -> integer" (\rhs -> return $ toASTExpr (Lit (IntLit (read (getText rhs 1)))) ),

      rule "Term -> string" (\rhs -> return $
          let str = read (getText rhs 1) :: String
          in  toASTExpr (Lit (StrLit str)) ),

      rule "Term -> boolean" (\rhs -> return $ toASTExpr (Lit (BoolLit (read (getText rhs 1)))) ),

      rule "Term -> ( )" (\rhs -> return $ toASTExpr (Lit UnitLit) ),

      rule "Term -> ( LExpr )" (\rhs -> return $ get rhs 2 )
    ],

    synCompSpec = Nothing,

    baseDir = "./",
    actionTblFile = "action_table.txt",
    gotoTblFile = "goto_table.txt",
    grammarFile = "prod_rules.txt",
    parserSpecFile = "mygrammar.grm",
    genparserexe = "yapb-exe"
  }
