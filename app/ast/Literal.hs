{-# LANGUAGE DeriveDataTypeable, DeriveGeneric #-}

module Literal where

import Type
import Text.JSON.Generic

import qualified Data.Aeson as DA
import GHC.Generics

import Data.Text.Prettyprint.Doc hiding (Pretty)
import Data.Text.Prettyprint.Doc.Util

data Literal =
    IntLit Int
  | StrLit String
  | BoolLit Bool
  | UnitLit
-- For aeson  
--  deriving (Show, Generic)
  deriving (Eq, Read, Show, Typeable, Data, Generic)

instance DA.FromJSON Literal
instance DA.ToJSON Literal

typeOfLiteral (IntLit _) = int_type
typeOfLiteral (StrLit _) = string_type
typeOfLiteral (BoolLit _) = bool_type
typeOfLiteral (UnitLit) = unit_type

trueLit  = "True"
falseLit = "False"
unitLit  = "()"

---
ppLit (IntLit i) = pretty (show i)
ppLit (StrLit s) = dquote <> pretty s <> dquote
ppLit (BoolLit b) = pretty (show b)
ppLit (UnitLit) = lparen <> rparen
