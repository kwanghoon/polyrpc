{-# LANGUAGE DeriveDataTypeable, DeriveGeneric #-}

module Runtime where

import Literal
import Prim
import Location

import qualified Data.Aeson as DA
import Control.Monad.Trans.State.Lazy
import Control.Monad.IO.Class
import qualified Data.Map as Map
import Text.JSON.Generic
import Text.JSON.Pretty

import GHC.Generics

-- | Expressions

data Expr =
--    ValExpr Value
  -- Compile-time value
    Var String
    
  -- Runtime value
  | Lit Literal
  | Tuple [Value]
  | Constr String [Value]
  | Closure [Value] CodeName [String] -- values mixed with location values

  -- Runtime value
  | Addr Integer
  
  -- Monadic value
  | UnitM Value
  | BindM [BindingDecl] Expr
  | Req Value Value           -- Todo: Replace Req,Call,GenApp with proper exprs
  | Call Value Value
  | GenApp Value Value Value  -- ARGS: Location fun arg

  -- Expression
  | Let [BindingDecl] Expr
  | Case Value [Alternative]  -- including pi_i (V)
  | App Value Value
--  | TypeApp Value Type [Type]
--  | LocApp Value [Location]
  | Prim PrimOp [Value] [Value]
  deriving (Eq, Read, Show, Typeable, Data, Generic)

instance DA.FromJSON PrimOp
instance DA.ToJSON PrimOp

instance DA.FromJSON Expr
instance DA.ToJSON Expr

data Alternative =
    Alternative String [String] Expr
  | TupleAlternative [String] Expr
  deriving (Eq, Read, Show, Typeable, Data, Generic)

instance DA.FromJSON Alternative
instance DA.ToJSON Alternative

data BindingDecl =
    Binding Bool String Expr    -- isTop?
    deriving (Eq, Read, Show, Typeable, Data, Generic)

instance DA.FromJSON BindingDecl
instance DA.ToJSON BindingDecl


-- | Values

type Value = Expr

data CodeName =
    CodeName String    -- fname (no location values and no types)
  deriving (Eq, Read, Show, Typeable, Data, Generic)

instance DA.FromJSON CodeName
instance DA.ToJSON CodeName


-----------------------------
-- | For static function map
-----------------------------

data Code =
    Code [String] OpenCode --  [free var or possibley free loc var]. OpenCode  (and no alphas)
    deriving (Read, Show, Typeable, Data, Generic)

data OpenCode =
    CodeAbs [String] Expr -- normal or location value argument
    deriving (Read, Show, Typeable, Data, Generic)
    
type FunctionMap = [(String, Code)]

data FunctionStore = FunctionStore
   { _clientstore :: FunctionMap
   , _serverstore :: FunctionMap
   }

-----------------------------
-- | For runtime function map
-----------------------------

type Env = [(String, Value)]

data RuntimeCode =
    RuntimeCode [String] RuntimeOpenCode --  [free var or possibley free loc var]. OpenCode  (and no alphas)
    
data RuntimeOpenCode =
    RuntimeCodeAbs [String] (Env -> Value -> RuntimeM Value) -- normal or location value argument

type RuntimeFunctionMap = [(String, RuntimeCode)]


-- Constructor names
reqName = "REQ"

callName = "CALL"

unitName = "UNIT"

---------------------------------------------------------------------
-- | Common send and receive  in loop_req, loop_call, and loop_server
---------------------------------------------------------------------
send :: Value -> RuntimeM ()
send v = do
  (mem, _send, _receive) <- get
  mem' <- liftIO $ _send mem v
  put (mem', _send, _receive)
  return ()

receive :: RuntimeM Value
receive = do
  (mem,_send,_receive) <- get
  (v, mem') <- liftIO $ _receive mem
  put (mem', _send, _receive)
  return v
---------------------------------------------------------------------

-- JSON
toJsonString :: Value -> String
toJsonString v = render $ pp_value $ toJSON v

-- Apply
apply :: RuntimeFunctionMap -> Value -> Value -> RuntimeM Value
apply funMap clo@(Closure freeVals (CodeName f) optrecf) w =  -- Tofix: optrecf !!
  case [ code | (g, code) <- funMap, f == g ] of
    (RuntimeCode fvars (RuntimeCodeAbs [_] action) :_) ->
       let recenv = case optrecf of
                      [recf] -> [(recf,clo)]
                      _ -> []
           closed_freeVals = map (doSubst recenv) freeVals
           env = zip fvars closed_freeVals 
       in  action env w
    (RuntimeCode fvars (RuntimeCodeAbs xs action) :_) ->
      error $ "apply: not a single argument in CodeAbs: " ++ show xs
    [] -> error $ "apply: not found in funMap: " ++ f

apply funMap clo w = 
  error $ "apply: not a closure: " ++ show clo ++ ", " ++ show w

req :: RuntimeFunctionMap -> Value -> Value -> RuntimeM Value
req funMap f arg = do
  send $ Constr reqName [f, arg]
  loop_req funMap

call :: RuntimeFunctionMap -> Value -> Value -> RuntimeM Value
call funMap f arg = do
  send $ Constr callName [f, arg]
  loop_call funMap

loop_req :: RuntimeFunctionMap -> RuntimeM Value   -- A hack: Used RuntimeFunctionMap instead of ()
loop_req funMap = do
  x <- receive
  case x of
    Constr "UNIT" [v] ->
      return $ v
      
    Constr "CALL" [f, arg] -> do
      w <- apply funMap f arg
      case w of
        UnitM warg -> do
          send (Constr "UNIT" [w])  -- i.e., UNIT (UnitM value)
          loop_req funMap
        _ -> error $ "[Runtime:loop_req] UnitM: Unexpected: " ++ show w

    _ -> error $ "[Runtime:loop_req] Unexpected: neither UNIT nor CALL" ++ show x

loop_call :: RuntimeFunctionMap -> RuntimeM Value
loop_call funMap = do
  x <- receive
  case x of
    Constr "UNIT" [v] ->
      return $ v
      
    Constr "REQ" [f, arg] -> do
      w <- apply funMap f arg
      case w of
        UnitM warg -> do
          send (Constr "UNIT" [w])  -- i.e., UNIT (UnitM value)
          loop_call funMap
        _ -> error $ "[Runtime:loop_call] UnitM: Unexpected: " ++ show w

    _ -> error $ "[Runtime:loop_req] Unexpected: neither UNIT nor REQ" ++ show x

loop_server :: RuntimeFunctionMap -> RuntimeM ()
loop_server funMap = do
  x <- receive
  case x of
    Constr "REQ" [f, arg] -> do
      w <- apply funMap f arg
      case w of
        UnitM warg -> do
          send (Constr "UNIT" [w])  -- i.e., UNIT (UnitM value)
          loop_server funMap
        _ -> error $ "[Runtime:loop_server] UnitM: Unexpected: " ++ show w

    _ -> error $ "[Runtime:loop_req] Unexpected: Not REQ" ++ show x


-- | Memory

data Mem = Mem { _new :: Integer, _map :: Map.Map Addr Value, _reg :: Maybe Value }
  deriving Eq

type Addr = Integer

initMem = Mem { _new=1, _map=Map.empty, _reg=Nothing }

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

type RuntimeState = (Mem, Mem -> Value -> IO Mem, Mem -> IO (Value, Mem))

type RuntimeM = StateT RuntimeState IO

--
prim :: PrimOp -> [Value] -> [Value] -> RuntimeM Value
prim op locvals argvals = do
  (mem,_send,_receive) <- get
  (v, mem') <- liftIO $ calc op locvals argvals mem
  put (mem',_send,_receive)
  return v
  
  where
    -- ToDo: Fix the duplicate code!
    
    -- calc :: PrimOp -> [Location] -> [Type] -> [Value] -> Mem -> IO (Value, Mem)
    calc :: PrimOp -> [Value] -> [Value] -> Mem -> IO (Value, Mem)

    -- calc MkRecOp locs [Closure vs codename [], Lit (StrLit f)] mem =
    --   return (Closure vs fvtys codename [f], mem)

    -- calc MkRecOp locs vs mem =
    --   error $ "[MkRecOp]: Unexpected: "
    --               ++ show locs ++ " " ++ show vs

    calc PrimRefCreateOp [loc1] [v] mem =
      let (addr, mem1) = allocMem v mem in return (Addr addr, mem1)

    calc PrimRefCreateOp locs vs mem =
      error $ "[PrimOp] PrimRefCreateOp: Unexpected: "
                  ++ show locs ++ " " ++ " " ++ show vs

    calc PrimRefReadOp [loc1] [Addr addr] mem = return (readMem addr mem, mem)

    calc PrimRefReadOp locs vs mem =
      error $ "[PrimOp] PrimRefReadOp: Unexpected: "
                  ++ show locs ++ " " ++ " " ++ show vs

    calc PrimRefWriteOp [loc1] [Addr addr,v] mem =
      return (Lit UnitLit, writeMem addr v mem)

    calc PrimRefWriteOp locs vs mem =
      error $ "[PrimOp] PrimRefWriteOp: Unexpected: "
                  ++ show locs ++ " " ++ " " ++ show vs

    calc PrimReadOp [loc] [Lit (UnitLit)] mem = do
      line <- getLine
      return (Lit (StrLit line), mem)

    calc PrimPrintOp [loc] [Lit (StrLit s)] mem = do
      putStr s
      return (Lit UnitLit, mem)


    calc primop locs vs mem =
      return (Lit $ calc' primop locs (map getLit vs), mem)

      where
        getLit (Lit lit) = lit
        getLit v = error $ "[Execute] calc-getLit: what? " ++ show v

    -- Primitives
    -- calc' :: PrimOp -> [Location] -> [Type] -> [Literal] -> Literal
    calc' :: PrimOp -> [Value] -> [Literal] -> Literal

    calc' NotPrimOp [loc] [BoolLit b] = BoolLit (not b)  -- loc is the current location

    calc' OrPrimOp [loc] [BoolLit x, BoolLit y] = BoolLit (x || y)

    calc' AndPrimOp [loc] [BoolLit x, BoolLit y] = BoolLit (x && y)

    calc' EqStringPrimOp [loc] [StrLit x, StrLit y] = BoolLit (x==y)

    calc' EqBoolPrimOp [loc] [BoolLit x, BoolLit y] = BoolLit (x==y)

    calc' EqIntPrimOp [loc] [IntLit x, IntLit y] = BoolLit (x==y)

    calc' NeqStringPrimOp [loc] [StrLit x, StrLit y] = BoolLit (x/=y)

    calc' NeqBoolPrimOp [loc] [BoolLit x, BoolLit y] = BoolLit (x/=y)

    calc' NeqIntPrimOp [loc] [IntLit x, IntLit y] = BoolLit (x/=y)

    calc' LtPrimOp [loc] [IntLit x, IntLit y] = BoolLit (x<y)

    calc' LePrimOp [loc] [IntLit x, IntLit y] = BoolLit (x<=y)

    calc' GtPrimOp [loc] [IntLit x, IntLit y] = BoolLit (x>y)

    calc' GePrimOp [loc] [IntLit x, IntLit y] = BoolLit (x>=y)

    calc' AddPrimOp [loc] [IntLit x, IntLit y] = IntLit (x+y)

    calc' SubPrimOp [loc] [IntLit x, IntLit y] = IntLit (x-y)

    calc' MulPrimOp [loc] [IntLit x, IntLit y] = IntLit (x*y)

    calc' DivPrimOp [loc] [IntLit x, IntLit y] = IntLit (x `div` y)

    calc' NegPrimOp [loc] [IntLit x] = IntLit (-x)

    -- Libraries
    calc' PrimIntToStringOp [loc] [IntLit i] = StrLit (show i)

    calc' PrimConcatOp [loc] [StrLit s1, StrLit s2] = StrLit (s1++s2)

    calc' operator locs operands =
      error $ "[PrimOp] Unexpected: "
         ++ show operator ++ " " ++ show locs ++ " " ++ " " ++ show operands

-- Reading R programs
load_expr :: String -> IO Expr
load_expr fileName = do
  text <- readFile fileName
  return $ read text

load_funstore :: String -> IO FunctionMap
load_funstore fileName = do
  text <- readFile fileName
  return $ read text

-------------------------------------------------------------------------------
-- | Interpreter for the untyped expressions
-------------------------------------------------------------------------------

interpFunMap :: String -> FunctionMap -> RuntimeFunctionMap
interpFunMap myloc rFunMap = funMap
  where
    funMap = interpFunMap' myloc rFunMap funMap

    interpFunMap' myloc rFunMap funMap =
      [ (f, RuntimeCode fvvars (RuntimeCodeAbs ys action))
      | (f, (Code fvvars (CodeAbs ys expr))) <- rFunMap,
        let  action = codeAbsToPair myloc (CodeAbs ys expr)
      ]

    codeAbsToPair myloc (CodeAbs [x] expr) =
      let actionExpr = interpExpr myloc expr in
      (\env v -> actionExpr funMap ([(x,v)] ++ env))
      
    codeAbsToPair myloc (CodeAbs xs expr) =
      error $ "interpFunMap: not a single arg var: " ++ show (length xs)

interpExpr :: String -> Expr -> RuntimeFunctionMap -> Env -> RuntimeM Value

interpExpr myloc expr =
  \ runtimeFunMap env -> do
      -- liftIO $ putStrLn ({- take 200 $ -} show $ doSubst env expr)
      interpExpr' myloc expr runtimeFunMap env
  
interpExpr' myloc (Var x) =
  \ runtimeFunMap env -> do
      let v = doSubst env (Var x)
      return v

interpExpr' myloc (Lit lit) = \ runtimeFunMap env -> return $ Lit lit

interpExpr' myloc (Tuple vs) =
  \ runtimeFunMap env -> do
      let closed_vs = map (doSubst env) vs
      return $ Tuple closed_vs

interpExpr' myloc (Constr cname vs) =
  \ runtimeFunMap env -> do
      let closed_vs = map (doSubst env) vs
      return $ Constr cname closed_vs

interpExpr' myloc (Closure fvs codeName recf) =
  \ runtimeFunMap env -> do
      let closed_fvs = map (doSubst env) fvs
      return $ Closure closed_fvs codeName recf

interpExpr' myloc (UnitM v) =
  \ runtimeFunMap env -> do
      liftIO $ putStrLn $ show $ doSubst env (UnitM v)

      let closed_v = doSubst env v
      return $ UnitM closed_v   -- (doSubst env v)

interpExpr' myloc (BindM [Binding b x bexpr] expr) =
  let actionBexpr = interpExpr myloc bexpr
      actionExpr = interpExpr myloc expr
  in 
  \ runtimeFunMap env -> do
      liftIO $ putStrLn $ show (Binding b x (doSubst env (bexpr)))
  
      mValue <- actionBexpr runtimeFunMap env
      case mValue of
        UnitM bValue -> actionExpr runtimeFunMap ([(x, bValue)] ++ env)
        _ -> error $ "[Runtime:interpExpr] BindM: Not UnitM: " ++ show mValue

interpExpr' myloc (BindM bindDecls expr) =
 error $ "[Runtime:interpExpr] BindM: not a single binding: " ++ show (length bindDecls)

interpExpr' myloc (Req f arg) =
  \ runtimeFunMap env -> do
     liftIO $ putStrLn $ show (doSubst env (Req f arg))
     
     let closed_f = doSubst env f 
     let closed_arg = doSubst env arg
     req runtimeFunMap closed_f closed_arg   -- (doSubst env f) (doSubst env arg)

interpExpr' myloc (Call f arg) =
  \ runtimeFunMap env -> do
     liftIO $ putStrLn $ show (doSubst env (Call f arg))
     
     let closed_f = doSubst env f
     let closed_arg = doSubst env arg
     call runtimeFunMap closed_f closed_arg  -- (doSubst env f) (doSubst env arg)

interpExpr' myloc (GenApp locval f arg) =
  \ runtimeFunMap env -> do
     liftIO $ putStrLn $ show (doSubst env (GenApp locval f arg))
     
     let closed_locval = doSubst env locval
     let closed_f = doSubst env f
     let closed_arg = doSubst env arg
  
     if myloc == clientLocName then
       case closed_locval of
         Constr fLoc [] ->
           if myloc == fLoc then apply runtimeFunMap closed_f closed_arg
           else req runtimeFunMap closed_f closed_arg
         _ -> error $ "[Runtime:interpExpr] GenApp@client: invalid location: " ++ show closed_locval
      
     else if myloc == serverLocName then
       case closed_locval of
         Constr fLoc [] ->
           if myloc == fLoc then apply runtimeFunMap closed_f closed_arg
           else call runtimeFunMap closed_f closed_arg
         _ -> error $ "[Runtime:interpExpr] GenApp@server: invalid location: " ++ show closed_locval

     else error $ "[Runtime:interpExpr] GenApp: unknown location: " ++ myloc

interpExpr' myloc (Let [Binding b x bexpr] expr) =
  let actionBexpr = interpExpr myloc bexpr
      actionExpr = interpExpr myloc expr
  in
  \ runtimeFunMap env -> do
      liftIO $ putStrLn $ show (Binding b x (doSubst env (bexpr)))
  
      bValue <- actionBexpr runtimeFunMap env
      actionExpr runtimeFunMap ([(x, bValue)] ++ env)

interpExpr' myloc (Let bindDecls expr) =
 error $ "[Runtime:interpExpr] BindM : not a single binding: " ++ show (length bindDecls)

interpExpr' myloc (Case value alts) =
  let actionAlts = interpAlts myloc alts
  in
  \ runtimeFunMap env -> do 
      liftIO $ putStrLn $ show $ doSubst env $ Case value []
      liftIO $ mapM_ (\alt -> case alt of
                                Alternative c xs _ -> putStrLn $ " " ++ c ++ " " ++ show xs
                                TupleAlternative xs _ -> putStrLn $ " " ++ show xs) alts
  
      let v = doSubst env value -- actionCaseVal runtimeFunMap env
      actionCase v actionAlts runtimeFunMap env
  where
    interpAlts myloc alts = 
      [ case alt of 
          Alternative dname xs expr -> (Just dname, xs, interpExpr myloc expr)
          TupleAlternative xs expr -> (Nothing, xs, interpExpr myloc expr)
      | alt <- alts ]

    actionCase v@(Constr cname args) actionAlts runtimeFunMap env = 
      case [ (xs, actionExpr)
           | (Just dname, xs, actionExpr) <- actionAlts, cname==dname ] of
        ((xs,actionExpr):_) 
          | length args == length xs -> do
              actionExpr runtimeFunMap (zip xs args ++ env)
          | otherwise -> error $ "[Runtime:interpExpr] case alt: arity mismatch: "
                           ++ show (length args) ++ " != " ++ show (length xs)
        [] -> error $ "[Runtime:interpExpr] case alt: no match for: " ++ show v

    actionCase v@(Tuple args) [(Nothing, xs, actionExpr)] runtimeFunMap env
      | length args == length xs = actionExpr runtimeFunMap (zip xs args ++ env)
      | otherwise = error $ "[Runtime:interpExpr] case alt: arity mismatch: "
                      ++ show (length args) ++ " != " ++ show (length xs)

    actionCase v@(Tuple args) _ runtimeFunMap env = 
      error $ "[Runtime:interpExpr] Not a single tuple aternative"

    actionCase v@(Lit (BoolLit b))
      [(Just b1, [], actionExpr1), (Just b2, [], actionExpr2)] runtimeFunMap env =
      let text_b = show b in
        if text_b==b1 then actionExpr1 runtimeFunMap env
        else if text_b==b2 then actionExpr2 runtimeFunMap env
        else error $ "[Runtime:interpExpr] Unexpected boolean aternative: "
                        ++ b1 ++ " and " ++ b2

    actionCase v actionAlts runtimeFunMap env = 
      error $ "[Runtime:interpExpr] Unexpected case value: " ++ show v

interpExpr' myloc (App f arg) =
  \ runtimeFunMap env -> do
      liftIO $ putStrLn $ show $ doSubst env $ App f arg
      
      let closed_f = doSubst env f
      let closed_arg = doSubst env arg
      apply runtimeFunMap closed_f closed_arg

interpExpr' myloc (Prim op locvals argvals) = 
  \ runtimeFunMap env -> do
      liftIO $ putStrLn $ show $ doSubst env $ Prim op locvals argvals
      
      let closed_locvals = map (doSubst env) locvals
      let closed_argvals = map (doSubst env) argvals
      prim op closed_locvals closed_argvals

interpExpr' myloc expr =
  error $ "[Runtime:interpExpr] Unexpected: " ++ show expr

-- | Substitution

doSubst :: [(String,Value)] -> Expr -> Expr

doSubst subst (Var x) =
  case [ v | (y,v) <- subst, x==y ] of
   (w : _) -> w
   _ -> Var x

doSubst subst (Lit lit) = Lit lit

doSubst subst (Tuple vs) = Tuple (map (doSubst subst) vs)

doSubst subst (Constr c vs) = Constr c (map (doSubst subst) vs)

doSubst subst (Closure fvs codeName recfs) =
  Closure (map (doSubst subst) fvs) codeName recfs

doSubst subst (Addr i) = Addr i

doSubst subst (UnitM v) = UnitM (doSubst subst v)

doSubst subst (BindM bindDecls expr) =
  let (subst1, bindDecls1) =
        foldl (\ (subst0, binds0) (Binding istop x expr) ->
           let subst1 = elim x subst0 in
             (subst1, binds0 ++ [Binding istop x (doSubst subst1 expr)])
        ) (subst, []) bindDecls
  in  BindM bindDecls1 (doSubst subst1 expr)

doSubst subst (Req f arg) = Req (doSubst subst f) (doSubst subst arg)

doSubst subst (Call f arg) = Call (doSubst subst f) (doSubst subst arg)

doSubst subst (GenApp locv f arg) =
  GenApp (doSubst subst locv) (doSubst subst f) (doSubst subst arg)

doSubst subst (Let bindDecls expr) =
  let (subst1, bindDecls1) =
        foldl (\ (subst0, binds0) (Binding istop x expr) ->
           let subst1 = elim x subst0 in
             (subst1, binds0 ++ [Binding istop x (doSubst subst1 expr)])
        ) (subst, []) bindDecls
  in  Let bindDecls1 (doSubst subst1 expr)

doSubst subst (Case v [TupleAlternative xs expr]) =
  let subst1 = elims xs subst
  in  Case (doSubst subst v)
        [ TupleAlternative xs (doSubst subst1 expr) ]

doSubst subst (Case v alts) =
  Case (doSubst subst v)
     (map (\ (Alternative cname xs expr) ->
             let subst1 = elims xs subst
             in  Alternative cname xs (doSubst subst1 expr)) alts)

doSubst subst (App f arg) = App (doSubst subst f) (doSubst subst arg)

doSubst subst (Prim op locvs vs) =
  Prim op (map (doSubst subst) locvs) (map (doSubst subst) vs)

--
elim x subst = [(y,e) | (y,e)<-subst, y/=x]

elims xs subst = foldl (\subst0 x0 -> elim x0 subst0) subst xs
