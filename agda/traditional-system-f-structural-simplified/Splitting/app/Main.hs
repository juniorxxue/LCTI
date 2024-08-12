{-# LANGUAGE MultiWayIf, LambdaCase, RankNTypes #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Redundant multi-way if" #-}
module Main where

import Debug.Trace


data Typ = TInt | TVar Int | TArr Typ Typ | TForall Typ deriving Eq
data Trm = Lit Int | Var Int | Abs Trm | App Trm Trm | Ann Trm Typ | TAbs Trm | TApp Trm Typ deriving Eq

instance Show Typ where
  show TInt = "Int"
  show (TVar i) = "t" ++ show i
  show (TArr t1 t2) = "(" ++ show t1 ++ " → " ++ show t2 ++ ")"
  show (TForall t) = "∀. " ++ show t

instance Show Trm where
  show (Lit i) = show i
  show (Var i) = "e" ++ show i
  show (Abs t) = "(λ. " ++ show t ++ ")"
  show (App t1 t2) = "(" ++ show t1 ++ " " ++ show t2 ++ ")"
  show (Ann t ty) = "(" ++ show t ++ " : " ++ show ty ++ ")"
  show (TAbs t) = "(Λ. " ++ show t ++ ")"
  show (TApp t ty) = "(" ++ show t ++ " [" ++ show ty ++ "])"

data Env = EEmpty | EBind Typ Env | ETyp Env | ESol Typ Env

instance Show Env where
  show EEmpty = "∅"
  show (EBind ty env) = show env ++ " , : " ++ show ty
  show (ETyp env) = show env ++ " , • "
  show (ESol ty env) = show env ++ " , =" ++ show ty

data Context = CEmpty | CFullType Typ | CTerm Trm Context | CTApp Typ Context

instance Show Context where
  show CEmpty = "□"
  show (CFullType ty) = show ty
  show (CTerm trm ctx) = "[" ++ show trm ++ "]" ++ " ↝ " ++ show ctx
  show (CTApp ty ctx) = "[" ++ show ty ++ "]" ++ " ↝ " ++ show ctx

-- shifting --

shiftTyp :: Int -> Typ -> Typ
shiftTyp _ TInt = TInt
shiftTyp k (TVar x) = if | x < k -> TVar x
                         | otherwise -> TVar (x + 1)
shiftTyp k (TArr t1 t2) = TArr (shiftTyp k t1) (shiftTyp k t2)
shiftTyp k (TForall t) = TForall (shiftTyp (k + 1) t)

shiftTyp0 :: Typ -> Typ
shiftTyp0 = shiftTyp 0

substTyp :: Int -> Typ -> Typ -> Typ
substTyp _ _ TInt = TInt
substTyp k tyA (TVar x) = if | k == x -> tyA
                             | otherwise -> TVar $ punchOut k x
                          where punchOut i j = if j > i then j - 1 else j
substTyp k tyA (TArr t1 t2) = TArr (substTyp k tyA t1) (substTyp k tyA t2)
substTyp k tyA (TForall tyB) = TForall (substTyp (k + 1) (shiftTyp0 tyA) tyB)

-- substTyp0 A B: subst A at 0th index in B
substTyp0 :: Typ -> Typ -> Typ
substTyp0 = substTyp 0

unshiftTyp0 :: Typ -> Typ
unshiftTyp0 = substTyp 0 TInt

shiftTerm :: Int -> Trm -> Trm
shiftTerm _ (Lit i) = Lit i
shiftTerm k (Var x) = if | x < k -> Var x
                         | otherwise -> Var (x + 1)
shiftTerm k (Abs t) = Abs (shiftTerm (k + 1) t)
shiftTerm k (App t1 t2) = App (shiftTerm k t1) (shiftTerm k t2)
shiftTerm k (Ann t ty) = Ann (shiftTerm k t) ty
shiftTerm k (TAbs t) = TAbs (shiftTerm k t)
shiftTerm k (TApp t ty) = TApp (shiftTerm k t) ty

shiftTerm0 :: Trm -> Trm
shiftTerm0 = shiftTerm 0

shiftContext :: Int -> Context -> Context
shiftContext _ CEmpty = CEmpty
shiftContext _ (CFullType ty) = CFullType ty
shiftContext k (CTerm trm ctx) = CTerm (shiftTerm k trm) (shiftContext k ctx)
shiftContext k (CTApp ty ctx) = CTApp ty (shiftContext k ctx)

shiftContext0 :: Context -> Context
shiftContext0 = shiftContext 0

shiftTypTrm :: Int -> Trm -> Trm
shiftTypTrm _ (Lit i) = Lit i
shiftTypTrm _ (Var x) = Var x
shiftTypTrm k (Abs t) = Abs (shiftTypTrm k t)
shiftTypTrm k (App t1 t2) = App (shiftTypTrm k t1) (shiftTypTrm k t2)
shiftTypTrm k (Ann t ty) = Ann (shiftTypTrm k t) (shiftTyp k ty)
shiftTypTrm k (TAbs t) = TAbs (shiftTypTrm (1 + k) t)
shiftTypTrm k (TApp t ty) = TApp (shiftTypTrm k t) (shiftTyp k ty)

shiftTypContext :: Int -> Context -> Context
shiftTypContext _ CEmpty = CEmpty
shiftTypContext k (CFullType ty) = CFullType (shiftTyp k ty)
shiftTypContext k (CTerm trm ctx) = CTerm (shiftTypTrm k trm) (shiftTypContext k ctx)
shiftTypContext k (CTApp ty ctx) = CTApp (shiftTyp k ty) (shiftTypContext k ctx)

shiftTypContext0 :: Context -> Context
shiftTypContext0 = shiftTypContext 0

-- end shifting --

data Apps = Nil | Cons Trm Apps | ConsTy Typ Apps
data AppsTyp = NilTyp | ConsTyp Typ AppsTyp | AppsForall AppsTyp

instance Show Apps where
  show Nil = "."
  show (Cons trm apps) = show trm ++ "; " ++ show apps
  show (ConsTy ty apps) = show ty ++ "; " ++ show apps

instance Show AppsTyp where
  show NilTyp = "."
  show (ConsTyp ty apps) = show ty ++ "; " ++ show apps
  show (AppsForall apps) = "∀. " ++ show apps

-- examples
-- split' (Cons TInt (Cons TInt Nil)) TInt (TForall (TArr (TVar 0) (TVar 0)))
split' :: AppsTyp -> Typ -> Typ -> AppsTyp
split' appstyp tyA tyB | trace ("split' " ++ show appstyp ++ " " ++ show tyA ++ " " ++ show tyB) False = undefined
split' NilTyp tyA tyB = NilTyp
-- split' (ConsTyp ty apps) tyA (TArr tyB1 tyB2) | substTyp0 tyA tyB1 == ty = ConsTyp ty (split' apps tyA tyB2)
split' (ConsTyp ty apps) tyA (TArr tyB1 tyB2) = ConsTyp ty (split' apps tyA tyB2)
split' (AppsForall apps) tyA (TForall tyB) = AppsForall (split' apps tyA tyB)

split :: Context -> Typ -> ((Apps, Context), (AppsTyp, Typ))
split CEmpty tyA = ((Nil, CEmpty), (NilTyp, tyA))
split (CFullType tyA) tyB = ((Nil, CFullType tyA), (NilTyp, tyB))
split (CTerm trm ctx) (TArr tyA tyB) = ((Cons trm apps, ctx'), (ConsTyp tyA appsTyp, ty))
                                      where ((apps, ctx'), (appsTyp, ty)) = split ctx tyB
split (CTApp tyA ctx) (TForall tyB) = ((ConsTy tyA apps, ctx'), (AppsForall appsTyp, tyC))
                                      where
                                        ((apps, ctx'), (appsTyp', tyC)) = split ctx (substTyp0 tyA tyB)
                                        appsTyp = split' appsTyp' tyA tyB


main :: IO ()
main = do
    -- print $ split (CTerm (Lit 1) CEmpty) (TArr TInt TInt)
    print $ split' (ConsTyp TInt (ConsTyp TInt NilTyp)) TInt (TForall (TArr (TVar 0) (TVar 0)))
    -- putStrLn "Hello, Haskell!"
