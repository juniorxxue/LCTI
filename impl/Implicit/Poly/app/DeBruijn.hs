{-# LANGUAGE MultiWayIf, LambdaCase, RankNTypes, TypeSynonymInstances #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Redundant multi-way if" #-}
module DeBruijn where

import Debug.Trace

import Syntax

-- shifting --

shiftTyp :: Int -> Typ -> Typ
shiftTyp _ TInt = TInt
shiftTyp k (TVar x) = if | x < k -> TVar x
                         | otherwise -> TVar (x + 1)
shiftTyp k (TArr t1 t2) = TArr (shiftTyp k t1) (shiftTyp k t2)
shiftTyp k (TForall t) = TForall (shiftTyp (k + 1) t)
shiftTyp k (TList t) = TList (shiftTyp k t)

shiftTyp0 :: Typ -> Typ
shiftTyp0 = shiftTyp 0

substTyp :: Int -> Typ -> Typ -> Typ
substTyp _ _ TInt = TInt
substTyp k tyA (TVar x) = if | k == x -> tyA
                             | otherwise -> TVar $ punchOut k x
                          where punchOut i j = if j > i then j - 1 else j
substTyp k tyA (TArr t1 t2) = TArr (substTyp k tyA t1) (substTyp k tyA t2)
substTyp k tyA (TForall tyB) = TForall (substTyp (k + 1) (shiftTyp0 tyA) tyB)
substTyp k tyA (TList tyB) = TList (substTyp k tyA tyB)

substTyp0 :: Typ -> Typ -> Typ
-- substTyp0 a b | trace ("substTyp0 " ++ show a ++ " " ++ show b) False = undefined
substTyp0 a b = substTyp 0 a b

unshiftTyp0 :: Typ -> Typ
-- unshiftTyp0 a | trace ("unshiftTyp0 " ++ show a) False = undefined
unshiftTyp0 a = substTyp 0 TInt a

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



-- type shift in term
shiftTyTerm :: Int -> Trm -> Trm
shiftTyTerm _ (Lit i) = Lit i
shiftTyTerm k (Var x) = (Var x)
shiftTyTerm k (Abs t) = Abs (shiftTyTerm k t)
shiftTyTerm k (App t1 t2) = App (shiftTyTerm k t1) (shiftTyTerm k t2)
shiftTyTerm k (Ann t ty) = Ann (shiftTyTerm k t) (shiftTyp k ty)
shiftTyTerm k (TAbs t) = TAbs (shiftTyTerm (1 + k) t)
shiftTyTerm k (TApp t ty) = TApp (shiftTyTerm k t) (shiftTyp k ty)

-- type shift in context
shiftTyContext :: Int -> Context -> Context
shiftTyContext _ CEmpty = CEmpty
shiftTyContext k (CFullType ty) = CFullType (shiftTyp k ty)
shiftTyContext k (CTerm trm ctx) = CTerm (shiftTyTerm k trm) (shiftTyContext k ctx)
shiftTyContext k (CTApp ty ctx) = CTApp (shiftTyp k ty) (shiftTyContext k ctx)

shiftTyContext0 :: Context -> Context
shiftTyContext0 = shiftTyContext 0

-- end shifting --
