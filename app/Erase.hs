{-# LANGUAGE DeriveDataTypeable, DeriveGeneric #-}

module Erase where

import qualified CSExpr as TE -- (Typed) Target expressions
import qualified UntypedCSExpr as UE  -- Untyped target expressions

erase :: TE.Expr -> IO UE.Expr
erase (TE.ValExpr v) = do
  uv <- eraseVal v
  return (UE.ValExpr uv)


eraseVal :: TE.Value -> IO UE.Value
eraseVal (TE.Lit lit) = return (UE.Lit lit)

