{-# LANGUAGE DeriveDataTypeable, DeriveGeneric #-}

module Prim where

import Text.JSON.Generic

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
  deriving (Eq, Read, Show, Typeable, Data)

-- Predefined type names
unitType   = "Unit"
intType    = "Int"
boolType   = "Bool"
stringType = "String"
refType    = "Ref"


