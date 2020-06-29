{-# LANGUAGE DeriveDataTypeable, DeriveGeneric #-}

module Erase where

import qualified CSExpr as TE

erase :: TE.Expr -> IO TE.Expr
erase pgm = return pgm

