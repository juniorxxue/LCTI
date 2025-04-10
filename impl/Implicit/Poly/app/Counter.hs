{-# LANGUAGE MultiWayIf #-}
module Counter where

import Syntax

data Counter = Inf | N Int

instance Show Counter where
  show Inf = "∞"
  show (N n) = show n

add :: Counter -> Counter -> Counter
add Inf _ = Inf
add _ Inf = Inf
add (N a) (N b) = N (a + b)

suc :: Counter -> Counter
suc Inf = Inf
suc (N n) = N (n + 1)

prd :: Counter -> Counter
prd Inf = Inf
prd (N n) | n > 0 = N (n - 1)
prd (N 0) = N 0

have :: Env -> Typ -> Counter
have env TInt = Inf
have env (TVar k) = if isEvar env k then N 0 else Inf
have env (TArr tyA tyB) = if closed env tyA
                          then suc $ have env tyB
                          else N 0
have env (TForall tyA) = have (EUvar env) tyA

need :: Trm -> Counter
need (Lit _) = N 0
need (Var _) = N 0
need (Abs e) = suc $ need e
need (App t1 t2) = prd (need t1)
need (Ann e tyA) = N 0
need (TAbs e) = need e
need (TApp e tyA) = need e
