{-# LANGUAGE DeriveDataTypeable, DeriveGeneric #-}

module Runtime where

import Literal
import Prim

import Text.JSON.Generic

data Value =
    Lit Literal
  | Tuple [Value]
  | Constr String [Value]
  | Closure [Value] CodeName [String] -- values mixed with location values
  deriving (Show, Typeable, Data)

data CodeName =
    CodeName String    -- fname (no location values and no types)
  deriving (Show, Typeable, Data)

data Code =
    Code [String] OpenCode --  [free var or possibley free loc var]. OpenCode  (and no alphas)

type Env = [(String, Value)]

data OpenCode =
    CodeAbs [String] (Env -> Value -> IO Value) -- normal or location value argument

type FunctionMap = [(String, Code)]


-- Constructor names
reqName = "REQ"

callName = "CALL"

unitName = "UNIT"

-- send and receive
send :: Value -> IO ()
send v = return () -- ToFix

receive :: IO Value
receive = return $ Tuple [] -- ToFix

apply :: FunctionMap -> Value -> Value -> IO Value
apply funMap clo@(Closure freeVals (CodeName f) optrecf) w =  -- Tofix: optrecf !!
  case [ code | (g, code) <- funMap, f == g ] of
    (Code fvars (CodeAbs [_] action) :_) ->
       let env = zip fvars freeVals ++
                 case optrecf of
                   [recf] -> [(recf,clo)]
                   _ -> []
       in  action env w
    (Code fvars (CodeAbs xs action) :_) ->
      error $ "apply: not a single argument in CodeAbs: " ++ show xs
    [] -> error $ "apply: not found in funMap: " ++ f

req :: FunctionMap -> Value -> Value -> IO Value
req funMap f arg = do
  send $ Constr reqName [f, arg]
  loop_req funMap

call :: FunctionMap -> Value -> Value -> IO Value
call funMap f arg = do
  send $ Constr callName [f, arg]
  loop_call funMap

loop_req :: FunctionMap -> IO Value   -- A hack: Used FunctionMap instead of ()
loop_req funMap = do
  x <- receive
  case x of
    Constr "UNIT" [v] ->
      return v
      
    Constr "CALL" [f, arg] -> do
      w <- apply funMap f arg
      send (Constr "UNIT" [w])
      loop_req funMap

loop_call :: FunctionMap -> IO Value
loop_call funMap = do
  x <- receive
  case x of
    Constr "UNIT" [v] ->
      return v
      
    Constr "REQ" [f, arg] -> do
      w <- apply funMap f arg
      send (Constr "UNIT" [w])
      loop_call funMap

loop_server :: FunctionMap -> IO Value
loop_server funMap = do
  x <- receive
  case x of
    Constr "REQ" [f, arg] -> do
      w <- apply funMap f arg
      send (Constr "UNIT" [w])
      loop_req funMap
      
--
prim :: PrimOp -> [Value] -> [Value] -> IO Value
prim op locvals argvals = return $ Tuple []  -- Tofix

