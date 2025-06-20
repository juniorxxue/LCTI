{-# LANGUAGE MultiWayIf #-}
module Counter where

import Debug.Trace

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

instance Eq Counter where
  Inf == Inf = True
  Inf == _ = False
  _ == Inf = False
  (N n) == (N m) = n == m

instance Ord Counter where
    compare Inf Inf = EQ
    compare Inf _ = GT
    compare _ Inf = LT
    compare (N n) (N m) = compare n m


isLessEqThan :: Counter -> Counter -> Bool
-- isLessEqThan c1 c2 | trace ("isLessEqThan " ++ show c1 ++ " " ++ show c2) False = undefined
isLessEqThan Inf _ = False
isLessEqThan _ Inf = True
isLessEqThan (N n) (N m) = n <= m
