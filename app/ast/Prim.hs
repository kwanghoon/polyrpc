{-# LANGUAGE DeriveDataTypeable, DeriveGeneric #-}

module Prim where

import GHC.Generics hiding (Prefix, Infix)
import Text.JSON.Generic

import Data.Text.Prettyprint.Doc hiding (Pretty)
import Data.Text.Prettyprint.Doc.Util

data PrimOp =
    NotPrimOp  --{l}. Bool -l-> Bool
  | OrPrimOp   --{l}. (Bool, Bool) -l-> Bool
  | AndPrimOp  --{l}. (Bool, Bool) -l-> Bool
  | EqPrimOp  --{l}. (?, ?) -l-> Bool    (Overloaded)
  | EqStringPrimOp  --{l}. (String, String) -l-> Bool
  | EqBoolPrimOp    --{l}. (Bool, Bool) -l-> Bool
  | EqIntPrimOp     --{l}. (Int, Int) -l-> Bool
  | NeqPrimOp  --{l}. (?, ?) -l-> Bool    (Overloaded)
  | NeqStringPrimOp  --{l}. (String, String) -l-> Bool
  | NeqBoolPrimOp  --{l}. (Bool, Bool) -l-> Bool
  | NeqIntPrimOp  --{l}. (Int, Int) -l-> Bool
  | LtPrimOp   --{l}. (Int, Int) -l-> Bool
  | LePrimOp   --{l}. (Int, Int) -l-> Bool
  | GtPrimOp   --{l}. (Int, Int) -l-> Bool
  | GePrimOp   --{l}. (Int, Int) -l-> Bool
  | AddPrimOp  --{l}. (Int, Int) -l-> Int
  | SubPrimOp  --{l}. (Int, Int) -l-> Int
  | MulPrimOp  --{l}. (Int, Int) -l-> Int
  | DivPrimOp  --{l}. (Int, Int) -l-> Int
  | NegPrimOp  --{l}. Int -l-> Int

  -- For basic libraries
  | PrimReadOp
  | PrimPrintOp
  | PrimIntToStringOp
  | PrimConcatOp
  | PrimRefCreateOp
  | PrimRefReadOp
  | PrimRefWriteOp

  -- For creating recursive closures
  -- | MkRecOp  -- MkRecOp closure f 
-- For aeson  
--  deriving (Show, Eq, Generic)
  deriving (Eq, Read, Show, Typeable, Data, Generic)

data Fixity = Prefix | Infix | Postfix deriving Show

fixity_info = [
    (NotPrimOp, Prefix)
  , (OrPrimOp, Infix)
  , (AndPrimOp, Infix)
  , (EqPrimOp, Infix)
  , (EqStringPrimOp, Infix)
  , (EqBoolPrimOp, Infix)
  , (NeqPrimOp, Infix)
  , (NeqStringPrimOp, Infix)
  , (NeqBoolPrimOp, Infix)
  , (NeqIntPrimOp, Infix)
  , (LtPrimOp, Infix)
  , (LePrimOp, Infix)
  , (GtPrimOp, Infix)
  , (GePrimOp, Infix)
  , (AddPrimOp, Infix)
  , (SubPrimOp, Infix)
  , (MulPrimOp, Infix)
  , (DivPrimOp, Infix)
  , (NegPrimOp, Prefix)
  ]

-- Predefined type names
unitType   = "Unit"
intType    = "Int"
boolType   = "Bool"
stringType = "String"
refType    = "Ref"

--
-- Todo: to implement ppPrim
ppPrim (NotPrimOp) = pretty "!"
ppPrim (OrPrimOp) = pretty "or"
ppPrim (AndPrimOp) = pretty "and"
ppPrim (EqPrimOp) = pretty "=="
ppPrim (EqStringPrimOp) = pretty "=="
ppPrim (EqBoolPrimOp) = pretty "=="
ppPrim (EqIntPrimOp) = pretty "=="
ppPrim (NeqPrimOp) = pretty "!="
ppPrim (NeqStringPrimOp) = pretty "!="
ppPrim (NeqBoolPrimOp) = pretty "!="
ppPrim (NeqIntPrimOp) = pretty "!="
ppPrim (LtPrimOp) = pretty "<"
ppPrim (LePrimOp) = pretty "<="
ppPrim (GtPrimOp) = pretty ">"
ppPrim (GePrimOp) = pretty ">="
ppPrim (AddPrimOp) = pretty "+"
ppPrim (SubPrimOp) = pretty "-"
ppPrim (MulPrimOp) = pretty "*"
ppPrim (DivPrimOp) = pretty "/"
ppPrim (NegPrimOp) = pretty "-"
