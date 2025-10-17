module DeBruijn where

import Syntax

-- shifting --

shiftTyp :: Int -> Typ -> Typ
shiftTyp _ TInt = TInt
shiftTyp _ TBool = TBool
shiftTyp k (TVar x)
  | x < k = TVar x
  | otherwise = TVar (x + 1)
shiftTyp k (TArr t1 t2) = TArr (shiftTyp k t1) (shiftTyp k t2)
shiftTyp k (TForall t) = TForall (shiftTyp (k + 1) t)
shiftTyp k (TUncurry ts t) = TUncurry (map (shiftTyp k) ts) (shiftTyp k t)
shiftTyp k (TList t) = TList (shiftTyp k t)
shiftTyp k (TProd t1 t2) = TProd (shiftTyp k t1) (shiftTyp k t2)
shiftTyp k (TST t1 t2) = TST (shiftTyp k t1) (shiftTyp k t2)

shiftTyp0 :: Typ -> Typ
shiftTyp0 = shiftTyp 0

substTyp :: Int -> Typ -> Typ -> Typ
substTyp _ _ TInt = TInt
substTyp _ _ TBool = TBool
substTyp k tyA (TVar x)
  | k == x = tyA
  | otherwise = TVar $ punchOut k x
  where
    punchOut i j = if j > i then j - 1 else j
substTyp k tyA (TArr t1 t2) = TArr (substTyp k tyA t1) (substTyp k tyA t2)
substTyp k tyA (TForall tyB) = TForall (substTyp (k + 1) (shiftTyp0 tyA) tyB)
substTyp k tyA (TUncurry ts tyB) = TUncurry (map (substTyp k tyA) ts) (substTyp k tyA tyB)
substTyp k tyA (TList tyB) = TList (substTyp k tyA tyB)
substTyp k tyA (TProd tyB1 tyB2) = TProd (substTyp k tyA tyB1) (substTyp k tyA tyB2)
substTyp k tyA (TST tyB1 tyB2) = TST (substTyp k tyA tyB1) (substTyp k tyA tyB2)

substTyp0 :: Typ -> Typ -> Typ
-- substTyp0 a b | trace ("substTyp0 " ++ show a ++ " " ++ show b) False = undefined
substTyp0 = substTyp 0

unshiftTyp0 :: Typ -> Typ
-- unshiftTyp0 a | trace ("unshiftTyp0 " ++ show a) False = undefined
unshiftTyp0 = substTyp 0 TInt

shiftTerm :: Int -> Trm -> Trm
shiftTerm _ (LitInt i) = LitInt i
shiftTerm _ (LitBool b) = LitBool b
shiftTerm k (Var x)
  | x < k = Var x
  | otherwise = Var (x + 1)
shiftTerm k (Abs t) = Abs (shiftTerm (k + 1) t)
shiftTerm k (AbsAnn ty t) = AbsAnn ty (shiftTerm (k + 1) t)
shiftTerm k (AbsUncurry n t) = AbsUncurry n (shiftTerm (k + n) t)
shiftTerm k (AbsUncurryAnn ts t) = AbsUncurryAnn ts (shiftTerm (k + length ts) t)
shiftTerm k (App t1 t2) = App (shiftTerm k t1) (shiftTerm k t2)
shiftTerm k (AppUncurry t ts) = AppUncurry (shiftTerm k t) (map (shiftTerm k) ts)
shiftTerm k (Ann t ty) = Ann (shiftTerm k t) ty
shiftTerm k (TAbs t) = TAbs (shiftTerm k t)
shiftTerm k (TApp t ty) = TApp (shiftTerm k t) ty
shiftTerm _ Nil = Nil
shiftTerm _ Cons = Cons
shiftTerm k (Pair t1 t2) = Pair (shiftTerm k t1) (shiftTerm k t2)
shiftTerm k (Fst t) = Fst (shiftTerm k t)
shiftTerm k (Snd t) = Snd (shiftTerm k t)
shiftTerm _ ST = ST
shiftTerm _ ConsUncurry = ConsUncurry
shiftTerm _ STUncurry = STUncurry

shiftTerm0 :: Trm -> Trm
shiftTerm0 = shiftTerm 0

shiftContext :: Int -> Context -> Context
shiftContext _ CEmpty = CEmpty
shiftContext _ (CFullType ty) = CFullType ty
shiftContext k (CTerm trm ctx) = CTerm (shiftTerm k trm) (shiftContext k ctx)
shiftContext k (CTApp ty ctx) = CTApp ty (shiftContext k ctx)
shiftContext k (CUncurry ts ctx) = CUncurry (map (shiftTerm k) ts) (shiftContext k ctx)
shiftContext k (CFst ctx) = CFst (shiftContext k ctx)
shiftContext k (CSnd ctx) = CSnd (shiftContext k ctx)

shiftContext0 :: Context -> Context
shiftContext0 = shiftContext 0

-- type shift in term
shiftTyTerm :: Int -> Trm -> Trm
shiftTyTerm _ (LitInt i) = LitInt i
shiftTyTerm _ (LitBool b) = LitBool b
shiftTyTerm _ (Var x) = Var x
shiftTyTerm k (Abs t) = Abs (shiftTyTerm k t)
shiftTyTerm k (AbsAnn ty t) = AbsAnn (shiftTyp k ty) (shiftTyTerm k t)
shiftTyTerm k (AbsUncurry n t) = AbsUncurry n (shiftTyTerm k t)
shiftTyTerm k (AbsUncurryAnn tys t) = AbsUncurryAnn (map (shiftTyp k) tys) (shiftTyTerm k t)
shiftTyTerm k (App t1 t2) = App (shiftTyTerm k t1) (shiftTyTerm k t2)
shiftTyTerm k (AppUncurry t ts) = AppUncurry (shiftTyTerm k t) (map (shiftTyTerm k) ts)
shiftTyTerm k (Ann t ty) = Ann (shiftTyTerm k t) (shiftTyp k ty)
shiftTyTerm k (TAbs t) = TAbs (shiftTyTerm (1 + k) t)
shiftTyTerm k (TApp t ty) = TApp (shiftTyTerm k t) (shiftTyp k ty)
shiftTyTerm _ Nil = Nil
shiftTyTerm _ Cons = Cons
shiftTyTerm k (Pair t1 t2) = Pair (shiftTyTerm k t1) (shiftTyTerm k t2)
shiftTyTerm k (Fst t) = Fst (shiftTyTerm k t)
shiftTyTerm k (Snd t) = Snd (shiftTyTerm k t)
shiftTyTerm _ ST = ST
shiftTyTerm _ ConsUncurry = ConsUncurry
shiftTyTerm _ STUncurry = STUncurry

-- type shift in context
shiftTyContext :: Int -> Context -> Context
shiftTyContext _ CEmpty = CEmpty
shiftTyContext k (CFullType ty) = CFullType (shiftTyp k ty)
shiftTyContext k (CTerm trm ctx) = CTerm (shiftTyTerm k trm) (shiftTyContext k ctx)
shiftTyContext k (CTApp ty ctx) = CTApp (shiftTyp k ty) (shiftTyContext k ctx)
shiftTyContext k (CUncurry ts ctx) = CUncurry (map (shiftTyTerm k) ts) (shiftTyContext k ctx)
shiftTyContext k (CFst ctx) = CFst (shiftTyContext k ctx)
shiftTyContext k (CSnd ctx) = CSnd (shiftTyContext k ctx)

shiftTyContext0 :: Context -> Context
shiftTyContext0 = shiftTyContext 0

-- end shifting --