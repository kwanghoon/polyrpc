module Simpl (simpl) where

import Location
import Prim
import Literal
import CSType
import CSExpr

import Data.HashMap.Strict

---------------------------------------------------------------------------
-- Simplification:
--
--   (1) simplify bound unit values
--      : BindM [ Binding x ty (ValExpr (UnitM v)) ] expr  ===>  expr [v/x]
--   (2) delete unused bound variables and function names
---------------------------------------------------------------------------

--
data UseInfo =
  UseInfo { cNameUseInfo :: HashMap String Int
          , varUseInfo   :: HashMap String Int }

initUseInfo = UseInfo { cNameUseInfo = empty, varUseInfo = empty }

---------------------
-- Simplify CS programs
---------------------

simpl :: Monad m => GlobalTypeInfo -> FunctionStore -> Expr
                     -> m (GlobalTypeInfo, FunctionStore, Expr)
simpl gti funStore mainexpr = do
  useInfo <-useAnalysis funStore mainexpr
  (funStore', mainexpr') <- doSimpl useInfo funStore mainexpr
  return (gti, funStore, mainexpr')

--------------------------------------------------------------------------------
-- Use analysis
--------------------------------------------------------------------------------
useAnalysis :: Monad m => FunctionStore -> Expr -> m UseInfo
useAnalysis funStore expr = do
  let initUseInfo = initUseInfoFrom funStore
  useInfo1 <- uaExpr initUseInfo expr
  useInfo2 <- uaFunStore useInfo1 funStore
  return useInfo2


initUseInfoFrom :: FunctionStore -> UseInfo
initUseInfoFrom funStore = UseInfo
  { cNameUseInfo =
      foldl (\hash x -> insert x 0 hash) empty
       ([ codeName | (codeName, _) <- _clientstore funStore ] ++
        [ codeName | (codeName, _) <- _serverstore funStore ])
  , varUseInfo = empty }


uaFunStore :: Monad m => UseInfo -> FunctionStore -> m UseInfo
uaFunStore useInfo funStore = return useInfo

uaExpr :: Monad m => UseInfo -> Expr -> m UseInfo
uaExpr useInfo expr = return useInfo

--------------------------------------------------------------------------------
-- Simplification
--------------------------------------------------------------------------------
doSimpl :: Monad m => UseInfo -> FunctionStore -> Expr -> m (FunctionStore, Expr)
doSimpl useInfo funstore expr = return (funstore, expr)
