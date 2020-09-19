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
data Used = C String Int  -- How many times this code name is used.
          | B String Int  -- How many times this bound variable is used.

-- initC cnames = Data.List.map (\cname -> C cname 0) cnames

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
  return (gti, funStore, mainexpr)
  -- useInfo <- useAnalysis initUseInfo funStore mainexpr
  -- (funStore', mainexpr') <- doSimpl useInfo funStore mainexpr
  -- return (gti, funStore', mainexpr')

useAnalysis :: Monad m => UseInfo -> FunctionStore -> Expr -> m UseInfo
useAnalysis useInfo funStore expr = return useInfo

doSimpl :: Monad m => UseInfo -> FunctionStore -> Expr -> m (FunctionStore, Expr)
doSimpl useInfo funStore expr = return (funStore, expr)

-- -------------------------
-- -- Simplify function stores
-- -------------------------

-- type GlobalInfo = (GlobalTypeInfo, FunctionStore)

-- simplFunStore :: Monad m => GlobalTypeInfo -> FunctionStore -> m FunctionStore
-- simplFunStore gti funStore = do
--   let clientFunStore = _clientstore funStore
--   let serverFunStore = _serverstore funStore

--   clientFunStore' <- mapM (simplFnCode gti clientLoc funStore) clientFunStore
--   serverFunStore' <- mapM (simplFnCode gti serverLoc funStore) serverFunStore

--   return $ funStore{_clientstore=clientFunStore', _serverstore=serverFunStore'}


-- simplFnCode :: Monad m => GlobalTypeInfo -> Location -> FunctionStore
--                         -> (String, (CodeType, Code)) -> m (String, (CodeType, Code))
-- simplFnCode gti loc funStore (f, (codety, code)) = do
--   code' <- simplCode (gti,funStore) loc codety code
--   return (f, (codety, code'))


-- simplCode gtigci loc (CodeType _freeLocVars _freeTyVars freeVarTys ty)
--                       (Code freeLocVars freeTyVars freeVars openCode) = do
--   let env = Env { _locVarEnv  = freeLocVars
--                 , _typeVarEnv = freeTyVars
--                 , _varEnv     = zip freeVars freeVarTys }

--   simplOpenCode gtigci loc env ty openCode




-- simplExpr gtigci loc env ty expr = return expr
