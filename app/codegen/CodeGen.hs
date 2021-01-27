module CodeGen where

import Location
import Prim
import Literal
import CSType
import CSExpr


codeGen :: Monad m => GlobalTypeInfo -> FunctionStore -> Expr -> m ()
codeGen t_gti funStore t_expr = return ()
