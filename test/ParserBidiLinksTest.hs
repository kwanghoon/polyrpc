module ParserBidiLinksTest(parserTests) where

-- It doesn't compile!!

import Test.HUnit

import Lexer
import qualified ParserBidiLinks as PBLinks

parserTests =
  [
    test1
  ]
  
test1 = TestCase (
  do datatypedecl_text = "data List a = Nil | Cons a (List a)"
  
     terminalList <- lexing lexerSpec datatypedecl_text
     exprSeqAst <- parsing PBLinks.parserSpec terminalList
     
     let exprs = fromASTTopLevelDeclSeq exprSeqAst
     assertEqual datatypedecl_text
      [ DataTypeTopLevel (DataType List [] ["a"]
         [ TypeCon "Nil" []
         , TypeCon "Cons" (TypeVarType "a") (ConType "List" [] [TypeVarType "a"]) ]) ]
      exprs
      
