{-# LANGUAGE DeriveDataTypeable, DeriveGeneric #-}

module Execute where

import Location
import Prim
import Literal
import CSType
import CSExpr hiding (Env(..), _new)
import CSSubst

import qualified Data.Map as Map
--import Text.JSON.Generic

data Mem = Mem { _new :: Integer, _map :: Map.Map Addr Value }

-- data Addr = Addr String Integer -- (loc,addr)
type Addr = Integer

initMem = Mem { _new=1, _map=Map.empty }

allocMem :: Value -> Mem -> (Addr, Mem)
allocMem v mem =
  let next = _new mem
      addrVals = _map mem
  in  (next, mem { _new=next+1, _map=Map.insert next v addrVals })

readMem :: Addr -> Mem -> Value
readMem addr mem =
  case Map.lookup addr (_map mem) of
   Just v -> v
   Nothing -> error $ "[readMem] Not found: " ++ show addr

writeMem :: Addr -> Value -> Mem -> Mem
writeMem addr v mem = mem { _map= Map.insert addr v (_map mem) }


-- Configuration

type EvalContext = Expr -> Expr

type Stack = [EvalContext]

data Config =
    ClientConfig [EvalContext] Expr Stack Mem Stack Mem  -- <E[M];Delta_c Mem_c | Delta_s Mem_s
  | ServerConfig Stack Mem [EvalContext] Expr Stack Mem  -- <Delta_c Mem_c | E[M];Delta_s Mem_s>
--  deriving (Show, Typeable, Data)


report :: Bool
report = False

--
execute :: Bool -> GlobalTypeInfo -> FunctionStore -> Expr -> IO Value
execute debug gti funStore mainExpr = do
  v <- run debug funStore (initConfig mainExpr)
  return v

assert b action = if b then action else return ()

--
run :: Bool -> FunctionStore -> Config -> IO Value

run debug funStore (ClientConfig [] (ValExpr (UnitM v)) [] mem_c [] mem_s) = do
  assert debug (putStrLn $ "[DONE]: [Client] " ++ show (ValExpr (UnitM v)) ++ "\n")

  return v

run debug funStore (ClientConfig evctx expr client_stack mem_c server_stack mem_s) = do
  assert debug (putStrLn $ "[STEP] [Client] " ++ show expr ++ "\n")
  assert debug (putStrLn $ "       EvCtx    " ++ showEvCxt evctx ++ "\n")
  assert debug (putStrLn $ "       c stk    " ++ showStack client_stack ++ "\n")
  assert debug (putStrLn $ "         mem    " ++ show (Map.toList $ _map mem_c) ++ "\n")
  assert debug (putStrLn $ "       s stk    " ++ showStack server_stack ++ "\n")
  assert debug (putStrLn $ "         mem    " ++ show (Map.toList $ _map mem_s) ++ "\n")

  config <- clientExpr funStore [] (applyEvCxt evctx expr) client_stack mem_c server_stack mem_s
  run debug funStore config

run debug funStore (ServerConfig client_stack mem_c evctx expr server_stack mem_s) = do
  assert debug (putStrLn $ "[STEP] [Server] " ++ show expr ++ "\n")
  assert debug (putStrLn $ "       EvCtx    " ++ showEvCxt evctx ++ "\n")
  assert debug (putStrLn $ "       c stk    " ++ showStack client_stack ++ "\n")
  assert debug (putStrLn $ "         mem    " ++ show (Map.toList $ _map mem_c) ++ "\n")
  assert debug (putStrLn $ "       s stk    " ++ showStack server_stack ++ "\n")
  assert debug (putStrLn $ "         mem    " ++ show (Map.toList $ _map mem_s) ++ "\n")

  config <- serverExpr funStore client_stack mem_c [] (applyEvCxt evctx expr) server_stack mem_s
  run debug funStore config

--
initConfig main_expr = ClientConfig [] main_expr [] initMem [] initMem

--
applyEvCxt [] expr = expr
applyEvCxt (evcxt:evcxts) expr = applyEvCxt evcxts (evcxt expr)

toFun [] = \x->x
toFun (evcxt:evcxts) = toFun evcxts . evcxt

showEvCxt cxt = show $ applyEvCxt cxt (ValExpr (Var "HOLE"))

showStack stk = show $ map showEvCxt [[cxt] | cxt <- stk]

-----------------------------------------------------------
-- < EvCtx[ Value]; Client stack | Server stack> ==> Config
-----------------------------------------------------------

clientExpr :: FunctionStore -> [EvalContext] -> Expr -> Stack -> Mem -> Stack -> Mem -> IO Config

clientExpr fun_store evctx (ValExpr v) client_stack mem_c server_stack mem_s =
  clientValue fun_store evctx v client_stack mem_c server_stack mem_s

-- (E-Let)
clientExpr fun_store evctx (Let [Binding istop x ty b@(ValExpr v)] expr) client_stack mem_c server_stack mem_s = do
  let subst = [(x,v)]
  return $ ClientConfig evctx (doSubstExpr subst expr) client_stack mem_c server_stack mem_s

-- (let x = Elet[] in M)
clientExpr fun_store evctx (Let [Binding istop x ty b@(_)] expr) client_stack mem_c server_stack mem_s = do
  clientExpr fun_store ((\bexpr->Let [Binding istop x ty bexpr] expr):evctx) b client_stack mem_c server_stack mem_s

-- (E-Proj-i) or (E-Tuple)
clientExpr fun_store evctx (Case (Tuple vs) casety [TupleAlternative xs expr]) client_stack mem_c server_stack mem_s = do
  let subst = zip xs vs
  return $ ClientConfig evctx (doSubstExpr subst expr) client_stack mem_c server_stack mem_s

-- (E-Proj-i) or (E-Data constructor) or (E-if)
clientExpr fun_store evctx (Case (Constr cname locs tys vs argtys) casety alts) client_stack mem_c server_stack mem_s = do
  case [(dname,xs,expr) | Alternative dname xs expr <- alts, cname==dname] of
    ((_,xs,expr):_) -> do
      let subst = zip xs vs
      return $ ClientConfig evctx (doSubstExpr subst expr) client_stack mem_c server_stack mem_s

    [] -> error $ "[clientExpr] Case alternative not found: " ++ cname

-- (E-Proj-i) or (E-Data constructor) or (E-if)
clientExpr fun_store evctx (Case (Lit (BoolLit b)) casety alts) client_stack mem_c server_stack mem_s = do
  let [Alternative b1 _ expr1,Alternative b2 _ expr2] = alts
  let text_b = show b
  if text_b==b1 then return $ ClientConfig evctx expr1 client_stack mem_c server_stack mem_s
  else if text_b==b2 then return $ ClientConfig evctx expr2 client_stack mem_c server_stack mem_s
  else error $ "[cilentExpr] Case unexpected: " ++ show b ++ "? " ++ b1 ++ " " ++ b2

-- (E-App)
clientExpr fun_store evctx (App clo@(Closure vs vstys codename recf) funty arg) client_stack mem_c server_stack mem_s = do
  assert report $ putStrLn "App-client"
  let CodeName fname locs tys = codename
  case [code | (gname,(codetype,code))<-_clientstore fun_store, fname==gname] of
    ((Code locvars tyvars fvvars (CodeAbs [(x,_)] expr)):_) -> do
      let subst    = [(x,arg)] ++ zip fvvars vs
      let substLoc = zip locvars locs
      let substTy  = zip tyvars tys
      let substed_expr = doRec clo recf $ doSubstExpr subst (doSubstTyExpr substTy (doSubstLocExpr substLoc expr))
      return $ ClientConfig evctx substed_expr client_stack mem_c server_stack mem_s

    [] -> error $ "[clientExpr] Client abs code not found: " ++ fname

-- (E-TApp)
-- clientExpr fun_store evctx (TypeApp clo@(Closure vs vstys codename recf) funty [argty]) client_stack mem_c server_stack mem_s = do
--   let CodeName fname locs tys = codename
--   case [code | (gname, (codetype,code))<-_clientstore fun_store, fname==gname] of
--     ((Code locvars tyvars fvvars (CodeTypeAbs [a] expr)):_) -> do
--       let subst    = zip fvvars vs
--       let substLoc = zip locvars locs
--       let substTy  = [(a,argty)] ++ zip tyvars tys
--       let substed_expr = doRec clo recf $ doSubstExpr subst (doSubstTyExpr substTy (doSubstLocExpr substLoc expr))
--       return $ ClientConfig evctx substed_expr client_stack mem_c server_stack mem_s

--     [] -> error $ "[clientExpr] Client tyabs code not found: " ++ fname

clientExpr fun_store evctx (TypeApp clo@(TypeAbs tyvars expr recf) funty argtys) client_stack mem_c server_stack mem_s = do
  case length tyvars == length argtys of
    True -> do
      let substTy  = zip tyvars argtys 
      let substed_expr = doRec clo recf $ doSubstTyExpr substTy expr
      return $ ClientConfig evctx substed_expr client_stack mem_c server_stack mem_s

    False -> error $ "[clientExpr] Client tyabs: |tyvars| != |argtys|: " ++ show (length tyvars) ++ "!=" ++ show (length argtys)

-- (E-LApp)
clientExpr fun_store evctx (LocApp clo@(Closure vs vstys codename recf) funty [argloc]) client_stack mem_c server_stack mem_s = do
  assert report $ putStrLn "LApp-client"
  let CodeName fname locs tys = codename
  case [code | (gname, (codetype,code))<-_clientstore fun_store, fname==gname] of
    ((Code locvars tyvars fvvars (CodeLocAbs [l] expr)):_) -> do
      let subst    = zip fvvars vs
      let substLoc = [(l,argloc)] ++ zip locvars locs
      let substTy  = zip tyvars tys
      let substed_expr = doRec clo recf $ doSubstExpr subst (doSubstTyExpr substTy (doSubstLocExpr substLoc expr))
      return $ ClientConfig evctx substed_expr client_stack mem_c server_stack mem_s

    [] -> error $ "[clientExpr] Client locabs code not found: " ++ fname

clientExpr fun_store evctx (Prim primop locs tys vs) client_stack mem_c server_stack mem_s = do
  (v, mem_c1) <- calc primop locs tys vs mem_c
  return $ ClientConfig evctx (ValExpr v) client_stack mem_c1 server_stack mem_s

clientExpr fun_store evctx expr client_stack mem_c server_stack mem_s =
  error $ "[clientExpr] Unexpected: " ++ show expr ++ "\n" ++ show (applyEvCxt evctx expr) ++ "\n"

--
clientValue :: FunctionStore -> [EvalContext] -> Value -> Stack -> Mem -> Stack -> Mem -> IO Config

-- (E-Unit-C)
clientValue fun_store [] (UnitM v) client_stack mem_c (top_evctx:server_stack) mem_s =
  return $ ServerConfig client_stack mem_c [] (top_evctx (ValExpr (UnitM v))) server_stack mem_s

-- (E-Req)
clientValue fun_store evctx (Req f funty arg) client_stack mem_c server_stack mem_s = do
  assert report $ putStrLn "Req-client"
  let client_stack1 = if null evctx then client_stack else (toFun evctx):client_stack
  return $ ServerConfig client_stack1 mem_c [] (App f funty arg) server_stack mem_s

-- (E-Gen-C-C) and (E-Gen-C-S)
clientValue fun_store evctx (GenApp loc f funty arg) client_stack mem_c server_stack mem_s = do
  assert report $ putStrLn "GenApp-client"
  if loc==clientLoc then
    return $ ClientConfig evctx (App f funty arg) client_stack mem_c server_stack mem_s
  else if loc==serverLoc then
    return $ ClientConfig evctx (ValExpr (Req f funty arg)) client_stack mem_c server_stack mem_s
  else
    error $ "[clientValue] GenApp: Unexpected location : " ++ show loc

-- (E-Do)
clientValue fun_store evctx (BindM [Binding istop x ty b@(ValExpr (UnitM v))] expr) client_stack mem_c server_stack mem_s = do
  let subst = [(x,v)]
  return $ ClientConfig evctx (doSubstExpr subst expr) client_stack mem_c server_stack mem_s

-- ( do x<-E[] in M )
clientValue fun_store evctx (BindM [Binding istop x ty b@(_)] expr) client_stack mem_c server_stack mem_s = do
  clientExpr fun_store ((\bexpr->ValExpr (BindM [Binding istop x ty bexpr] expr)):evctx) b client_stack mem_c server_stack mem_s

clientValue fun_store evctx v client_stack mem_c server_stack mem_s =
  error $ "[clientValue] Unexpected: " ++ show v ++ "\n" ++ show (applyEvCxt evctx (ValExpr v)) ++ "\n"


------------------------------------------------------------
-- < Client stack | EvCtx[ Value ]; Server stack> ==> Config
------------------------------------------------------------

serverExpr :: FunctionStore -> Stack -> Mem -> [EvalContext] -> Expr -> Stack -> Mem -> IO Config

serverExpr fun_store client_stack mem_c evctx (ValExpr v) server_stack mem_s =
  serverValue fun_store client_stack mem_c evctx v server_stack mem_s

-- (E-Let)
serverExpr fun_store client_stack mem_c evctx (Let [Binding istop x ty b@(ValExpr v)] expr) server_stack mem_s = do
  let subst = [(x,v)]
  return $ ServerConfig client_stack mem_c evctx (doSubstExpr subst expr) server_stack mem_s

-- (let x = Elet[] in M)
serverExpr fun_store client_stack mem_c evctx (Let [Binding istop x ty b@(_)] expr) server_stack mem_s = do
  serverExpr fun_store client_stack mem_c ((\bexpr->Let [Binding istop x ty bexpr] expr):evctx) b server_stack mem_s

-- (E-Proj-i) or (E-Tuple) or (E-if)
serverExpr fun_store client_stack mem_c evctx (Case (Tuple vs) casety [TupleAlternative xs expr]) server_stack mem_s = do
  let subst = zip xs vs
  return $ ServerConfig client_stack mem_c evctx (doSubstExpr subst expr) server_stack mem_s

-- (E-Proj-i) or (E-Data constructor) or (E-if)
serverExpr fun_store client_stack mem_c evctx (Case (Constr cname locs tys vs argtys) casety alts) server_stack mem_s = do
  case [(dname,xs,expr) | Alternative dname xs expr <- alts, cname==dname] of
    ((_,xs,expr):_) -> do
      let subst = zip xs vs
      return $ ServerConfig client_stack mem_c evctx (doSubstExpr subst expr) server_stack mem_s

    [] -> error $ "[serverExpr] Case alternative not found: " ++ cname

serverExpr fun_store client_stack mem_c evctx (Case (Lit (BoolLit b)) casety alts) server_stack mem_s = do
  let [Alternative b1 _ expr1,Alternative b2 _ expr2] = alts
  let text_b = show b
  if text_b==b1 then return $ ServerConfig client_stack mem_c evctx expr1 server_stack mem_s
  else if text_b==b2 then return $ ServerConfig client_stack mem_c evctx expr2 server_stack mem_s
  else error $ "[cilentExpr] Case unexpected: " ++ show b ++ "? " ++ b1 ++ " " ++ b2

-- (E-App)
serverExpr fun_store client_stack mem_c evctx (App clo@(Closure vs vstys codename recf) funty arg) server_stack mem_s = do
  assert report $ putStrLn "App-server"
  let CodeName fname locs tys = codename
  case [code | (gname,(codetyps,code))<-_serverstore fun_store, fname==gname] of
    ((Code locvars tyvars fvvars (CodeAbs [(x,_)] expr)):_) -> do
      let subst    = [(x,arg)] ++ zip fvvars vs
      let substLoc = zip locvars locs
      let substTy  = zip tyvars tys
      let substed_expr = doRec clo recf $ doSubstExpr subst (doSubstTyExpr substTy (doSubstLocExpr substLoc expr))
      return $ ServerConfig client_stack mem_c evctx substed_expr server_stack mem_s

    [] -> error $ "[serverExpr] Server abs code not found: " ++ fname

-- (E-TApp)
-- serverExpr fun_store client_stack mem_c evctx (TypeApp clo@(Closure vs vstys codename recf) funty [argty]) server_stack mem_s = do
--   let CodeName fname locs tys = codename
--   case [code | (gname, (codetype,code))<-_serverstore fun_store, fname==gname] of
--     ((Code locvars tyvars fvvars (CodeTypeAbs [a] expr)):_) -> do
--       let subst    = zip fvvars vs
--       let substLoc = zip locvars locs
--       let substTy  = [(a,argty)] ++ zip tyvars tys
--       let substed_expr = doRec clo recf $ doSubstExpr subst (doSubstTyExpr substTy (doSubstLocExpr substLoc expr))
--       return $ ServerConfig client_stack mem_c evctx substed_expr server_stack mem_s

--     [] -> error $ "[serverExpr] Server tyabs code not found: " ++ fname ++ "\n"
--                       ++ ", " ++ show [gname | (gname,_)<-_serverstore fun_store] ++ "\n"
--                       ++ ", " ++ show [gname | (gname,_)<-_clientstore fun_store] ++ "\n"

serverExpr fun_store client_stack mem_c evctx (TypeApp clo@(TypeAbs tyvars expr recf) funty argtys) server_stack mem_s = do
  case length tyvars == length argtys of
    True -> do
      let substTy  = zip tyvars argtys 
      let substed_expr = doRec clo recf $ doSubstTyExpr substTy expr
      return $ ServerConfig client_stack mem_c evctx substed_expr server_stack mem_s

    False -> error $ "[serverExpr] Server tyabs |tyvars| != |argtys|: " ++ show (length tyvars) ++ " != " ++ show (length argtys)

-- (E-LApp)
serverExpr fun_store client_stack mem_c evctx (LocApp clo@(Closure vs vstys codename recf) funty [argloc]) server_stack mem_s = do
  assert report $ putStrLn "LApp-server"
  let CodeName fname locs tys = codename
  case [code | (gname, (codetype,code))<-_serverstore fun_store, fname==gname] of
    ((Code locvars tyvars fvvars (CodeLocAbs [l] expr)):_) -> do
      let subst    = zip fvvars vs
      let substLoc = [(l,argloc)] ++ zip locvars locs
      let substTy  = zip tyvars tys
      let substed_expr = doRec clo recf $ doSubstExpr subst (doSubstTyExpr substTy (doSubstLocExpr substLoc expr))
      return $ ServerConfig client_stack mem_c evctx substed_expr server_stack mem_s

    [] -> error $ "[serverExpr] Server locabs code not found: " ++ fname

serverExpr fun_store client_stack mem_c evctx (Prim primop locs tys vs) server_stack mem_s = do
  (v, mem_s1) <- calc primop locs tys vs mem_s
  return $ ServerConfig client_stack mem_c evctx (ValExpr v) server_stack mem_s1


--
serverValue :: FunctionStore -> Stack -> Mem -> [EvalContext] -> Value -> Stack -> Mem -> IO Config

-- (E-Unit-S-E)
serverValue fun_store [] mem_c [] (UnitM v) [] mem_s =
  return $ ClientConfig [] (ValExpr (UnitM v)) [] mem_c [] mem_s

-- (E-Unit-S)
serverValue fun_store (top_evctx:client_stack) mem_c [] (UnitM v) server_stack mem_s =
  return $ ClientConfig [] (top_evctx (ValExpr (UnitM v))) client_stack mem_c server_stack mem_s

-- (E-Call)
serverValue fun_store client_stack mem_c evctx (Call f funty arg) server_stack mem_s = do
  assert report $ putStrLn "Call-server"
  let server_stack1 = if null evctx then server_stack else (toFun evctx):server_stack
  return $ ClientConfig [] (App f funty arg) client_stack mem_c server_stack1 mem_s

-- (E-Gen-C-C) and (E-Gen-S-C)
serverValue fun_store client_stack mem_c evctx (GenApp loc f funty arg) server_stack mem_s = do
  assert report $ putStrLn "GenApp-server"
  if loc==serverLoc then
    return $ ServerConfig client_stack mem_c evctx (App f funty arg) server_stack mem_s
  else if loc==clientLoc then
    return $ ServerConfig client_stack mem_c evctx (ValExpr (Call f funty arg)) server_stack mem_s
  else
    error $ "[serverValue] GenApp: Unexpected location : " ++ show loc

-- (E-Do)
serverValue fun_store client_stack mem_c evctx (BindM [Binding istop x ty b@(ValExpr (UnitM v))] expr) server_stack mem_s = do
  let subst = [(x,v)]
  return $ ServerConfig client_stack mem_c evctx (doSubstExpr subst expr) server_stack mem_s

-- ( do x<-E[] in M ) : b is one of BindM, Call, and GenApp.
serverValue fun_store client_stack mem_c evctx (BindM [Binding istop x ty b@(_)] expr) server_stack mem_s = do
  serverExpr fun_store client_stack mem_c ((\bexpr->ValExpr (BindM [Binding istop x ty bexpr] expr)):evctx) b server_stack mem_s

serverValue fun_store client_stack mem_c evctx v server_stack mem_s = do
  error $ "[serverValue]: Unexpected: " ++ show v ++ "\n"
                 ++ show [f | (f,_)<-_clientstore fun_store] ++ "\n"
                 ++ show [f | (f,_)<-_serverstore fun_store] ++ "\n"

-----------------------
-- Primitive operations
-----------------------

calc :: PrimOp -> [Location] -> [Type] -> [Value] -> Mem -> IO (Value, Mem)

-- calc MkRecOp locs tys [Closure vs fvtys codename [], Lit (StrLit f)] mem =
--   return (Closure vs fvtys codename [f], mem)

-- calc MkRecOp locs tys vs mem =
--   error $ "[MkRecOp]: Unexpected: "
--               ++ show locs ++ " " ++ show tys ++ " " ++ show vs

calc PrimRefCreateOp [loc1] [ty] [v] mem =
  let (addr, mem1) = allocMem v mem in return (Addr addr, mem1)

calc PrimRefCreateOp locs tys vs mem =
  error $ "[PrimOp] PrimRefCreateOp: Unexpected: "
              ++ show locs ++ " " ++ show  tys ++ " " ++ show vs

calc PrimRefReadOp [loc1] [ty] [Addr addr] mem = return (readMem addr mem, mem)

calc PrimRefReadOp locs tys vs mem =
  error $ "[PrimOp] PrimRefReadOp: Unexpected: "
              ++ show locs ++ " " ++ show  tys ++ " " ++ show vs

calc PrimRefWriteOp [loc1] [ty] [Addr addr,v] mem =
  return (Lit UnitLit, writeMem addr v mem)

calc PrimRefWriteOp locs tys vs mem =
  error $ "[PrimOp] PrimRefWriteOp: Unexpected: "
              ++ show locs ++ " " ++ show  tys ++ " " ++ show vs

calc PrimReadOp [loc] [] [Lit (UnitLit)] mem = do
  line <- getLine
  return (Lit (StrLit line), mem)

calc PrimPrintOp [loc] [] [Lit (StrLit s)] mem = do
  putStr s
  return (Lit UnitLit, mem)


calc primop locs tys vs mem =
  return (Lit $ calc' primop locs tys (map getLit vs), mem)

  where
    getLit (Lit lit) = lit
    getLit v = error $ "[Execute] calc-getLit: what? " ++ show v
                       ++ "\n  in " ++ show (Prim primop locs tys vs)

-- Primitives
calc' :: PrimOp -> [Location] -> [Type] -> [Literal] -> Literal

calc' NotPrimOp [loc] [] [BoolLit b] = BoolLit (not b)  -- loc is the current location

calc' OrPrimOp [loc] [] [BoolLit x, BoolLit y] = BoolLit (x || y)

calc' AndPrimOp [loc] [] [BoolLit x, BoolLit y] = BoolLit (x && y)

calc' EqStringPrimOp [loc] [] [StrLit x, StrLit y] = BoolLit (x==y)

calc' EqBoolPrimOp [loc] [] [BoolLit x, BoolLit y] = BoolLit (x==y)

calc' EqIntPrimOp [loc] [] [IntLit x, IntLit y] = BoolLit (x==y)

calc' NeqStringPrimOp [loc] [] [StrLit x, StrLit y] = BoolLit (x/=y)

calc' NeqBoolPrimOp [loc] [] [BoolLit x, BoolLit y] = BoolLit (x/=y)

calc' NeqIntPrimOp [loc] [] [IntLit x, IntLit y] = BoolLit (x/=y)

calc' LtPrimOp [loc] [] [IntLit x, IntLit y] = BoolLit (x<y)

calc' LePrimOp [loc] [] [IntLit x, IntLit y] = BoolLit (x<=y)

calc' GtPrimOp [loc] [] [IntLit x, IntLit y] = BoolLit (x>y)

calc' GePrimOp [loc] [] [IntLit x, IntLit y] = BoolLit (x>=y)

calc' AddPrimOp [loc] [] [IntLit x, IntLit y] = IntLit (x+y)

calc' SubPrimOp [loc] [] [IntLit x, IntLit y] = IntLit (x-y)

calc' MulPrimOp [loc] [] [IntLit x, IntLit y] = IntLit (x*y)

calc' DivPrimOp [loc] [] [IntLit x, IntLit y] = IntLit (x `div` y)

calc' NegPrimOp [loc] [] [IntLit x] = IntLit (-x)

-- Libraries
calc' PrimIntToStringOp [loc] [] [IntLit i] = StrLit (show i)

calc' PrimConcatOp [loc] [] [StrLit s1, StrLit s2] = StrLit (s1++s2)

calc' operator locs tys operands =
  error $ "[PrimOp] Unexpected: "
     ++ show operator ++ " " ++ show locs ++ " " ++ show tys ++ " " ++ show operands


--
doRec clo [] expr = expr
doRec (Closure vs tys codename recf) [f] expr = doSubstExpr [(f, Closure vs tys codename [f])] expr
doRec (TypeAbs tyvars body_expr recf) [f] expr = doSubstExpr [(f, TypeAbs tyvars body_expr [f])] expr
doRec clo recf expr = error $ "[doRec] Unexpected" ++ show clo ++ ", " ++ show recf ++ ", " ++ show expr

