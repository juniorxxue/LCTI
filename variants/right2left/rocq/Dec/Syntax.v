Require Import Coq.Init.Nat.
Require Import Coq.Arith.Compare_dec.

Inductive Typ : Set :=
| Int  : Typ
| TVar : nat -> Typ
| Arr  : Typ -> Typ -> Typ
| All  : Typ -> Typ.

(* notations are only used for displaying *)
Notation "‶ X"     := (TVar X) (at level 13, right associativity).
Notation "A `→ B" := (Arr A B) (at level 11, right associativity).
Notation "`∀ A"    := (All A) (at level 12, right associativity).

Inductive Trm : Set :=
| Lit   : nat -> Trm
| Var   : nat -> Trm
| Lam   : Trm -> Trm
| App   : Trm -> Trm -> Trm
| Ann   : Trm -> Typ -> Trm
| TLam  : Trm -> Trm
| TApp  : Trm -> Typ -> Trm.

Notation "ƛ~ e"     := (Lam e) (at level 51, right associativity).
Notation "e1 · e2"  := (App e1 e2) (at level 40, left associativity).
Notation "e ⦂ A"    := (Ann e A) (at level 50, left associativity).
Notation "Λ~ e"     := (TLam e) (at level 52, right associativity).
Notation "e @ A "   := (TApp e A) (at level 50, left associativity).

Inductive Context : Set :=
| CtxEmpty : Context
| CtxTyp   : Typ -> Context
| CtxTrm   : Trm -> Context -> Context.

Notation "■"        := CtxEmpty (at level 50).
Notation "τ~ A"      := (CtxTyp A) (at level 50).
Notation "[ e ]↝ Σ" := (CtxTrm e Σ) (at level 53, right associativity).

Inductive NonEmpty : Context -> Prop :=
| ne_τ    : forall A,   NonEmpty (CtxTyp A)
| ne_app  : forall e Σ, NonEmpty (CtxTrm e Σ).

(* Inductive GenericConsumer : Trm -> Prop :=
| gc_i    : forall n,   GenericConsumer (Lit n)
| gc_var  : forall x,   GenericConsumer (Var x)
| gc_ann  : forall e A, GenericConsumer (Ann e A)
| gc_tlam : forall e,   GenericConsumer (TLam e). *)

Definition GenericConsumer (e : Trm) : Prop :=
  match e with
  | Lit n     => True
  | Var x     => True
  | Ann e A   => True
  | TLam e    => True
  | _         => False
  end.

(* The environment is a list of types, and the existential variables are in the tail *)

Inductive Env : Set :=
| EnvEmpty  : Env
| TmCons    : Env -> Typ -> Env
| ExCons    : Env -> Env
| TyCons    : Env -> Env
| ExTyCons  : Env -> Typ -> Env
| SepCons   : Env -> Env.

Notation "∅"       := EnvEmpty (at level 60).
Notation "Γ , A"   := (TmCons Γ A) (at level 60, right associativity).
Notation "Γ , ^"   := (ExCons Γ) (at level 60, right associativity).
Notation "Γ , ⋅"   := (TyCons Γ) (at level 60, right associativity).
Notation "Γ , = A" := (ExTyCons Γ A) (at level 60, right associativity).
Notation "Γ ⋈"     := (SepCons Γ) (at level 55, right associativity).

(* The function f(i,j) = if i<=j then j+1 else j *)
Definition punchIn (k : nat) (X : nat) : nat :=
  if k <=? X then S X else X.

Fixpoint ty_shift (A : Typ) (k : nat) : Typ :=
  match A with
  | Int     => Int
  | TVar X  => TVar (punchIn k X)
  | Arr A B => Arr (ty_shift A k) (ty_shift B k)
  | All A   => All (ty_shift A (S k))
  end.

Fixpoint tm_shift (e : Trm) (k : nat) : Trm :=
  match e with
  | Lit n     => Lit n
  | Var x     => Var (punchIn k x)
  | Lam e     => Lam (tm_shift e (S k))
  | App e1 e2 => App (tm_shift e1 k) (tm_shift e2 k)
  | Ann e A   => Ann (tm_shift e k) A
  | TLam e    => TLam (tm_shift e k)
  | TApp e A  => TApp (tm_shift e k) A
  end.

Fixpoint ty_shift_tm (e : Trm) (k : nat) : Trm :=
  match e with
  | Lit n     => Lit n
  | Var x     => Var x
  | Lam e     => Lam (ty_shift_tm e k)
  | App e1 e2 => App (ty_shift_tm e1 k) (ty_shift_tm e2 k)
  | Ann e A   => Ann (ty_shift_tm e k) (ty_shift A k)
  | TLam e    => TLam (ty_shift_tm e (S k))
  | TApp e A  => TApp (ty_shift_tm e k) (ty_shift A k)
  end.

Fixpoint ty_shift_ctx (Σ : Context) (k : nat) : Context :=
  match Σ with
  | CtxEmpty    => CtxEmpty
  | CtxTyp A    => CtxTyp (ty_shift A k)
  | CtxTrm e Σ  => CtxTrm (ty_shift_tm e k) (ty_shift_ctx Σ k)
  end.

Fixpoint tm_shift_ctx (Σ : Context) (k : nat) : Context :=
  match Σ with
  | CtxEmpty    => CtxEmpty
  | CtxTyp A    => CtxTyp A
  | CtxTrm e Σ  => CtxTrm (tm_shift e k) (tm_shift_ctx Σ k)
  end.

(* lookup an entry: term variable, won't bypass the ⋈, since assume in TypEnv *)
Inductive lookupTm : Env -> nat -> Typ -> Prop :=
| l_tm_Z     : forall Γ A, lookupTm (TmCons Γ A) 0 A
| l_tm_STm   : forall Γ A B x, lookupTm Γ x A -> lookupTm (TmCons Γ B) (S x) A
| l_tm_STy   : forall Γ A x, lookupTm Γ x A -> lookupTm (TyCons Γ) x (ty_shift A 0)
| l_tm_SEx   : forall Γ x A, lookupTm Γ x A -> lookupTm (ExCons Γ) x (ty_shift A 0)
| l_tm_SExTy : forall Γ A B x, lookupTm Γ x A -> lookupTm (ExTyCons Γ B) x (ty_shift A 0).

(* lookup an entry: universal variable *)
Inductive lookupTy : Env -> nat -> Prop :=
| l_ty_Z     : forall Γ, lookupTy (TyCons Γ) 0
| l_ty_STm   : forall Γ A x, lookupTy Γ x -> lookupTy (TmCons Γ A) x
| l_ty_STy   : forall Γ x, lookupTy Γ x -> lookupTy (TyCons Γ) (S x)
| l_ty_SExTy : forall Γ A x, lookupTy Γ x -> lookupTy (ExTyCons Γ A) (S x)
| l_ty_SEx   : forall Γ x, lookupTy Γ x -> lookupTy (ExCons Γ) (S x)
| l_ty_SSep  : forall Γ x, lookupTy Γ x -> lookupTy (SepCons Γ) x.

(* lookup an entry in subtyping env: (unsolved) existential variable *)
Inductive lookupEx : Env -> nat -> Prop :=
| l_ex_Z     : forall Γ, lookupEx (ExCons Γ) 0
| l_ex_STm   : forall Γ A x, lookupEx Γ x -> lookupEx (TmCons Γ A) x
| l_ex_STy   : forall Γ x, lookupEx Γ x -> lookupEx (TyCons Γ) (S x)
| l_ex_SEx   : forall Γ x, lookupEx Γ x -> lookupEx (ExCons Γ) (S x)
| l_ex_SExTy : forall Γ A x, lookupEx Γ x -> lookupEx (ExTyCons Γ A) (S x)
| l_ex_SSep  : forall Γ x, lookupEx Γ x -> lookupEx (SepCons Γ) x.

(* lookup an entry in subtyping env : solution *)
Inductive lookupExTy : Env -> nat -> Typ -> Prop :=
| l_exty_Z      : forall Γ A, lookupExTy (ExTyCons Γ A) 0 (ty_shift A 0)
| l_exty_STy    : forall Γ A x, lookupExTy Γ x A -> lookupExTy (TyCons Γ) (S x) (ty_shift A 0)
| l_exty_SEx    : forall Γ A x, lookupExTy Γ x A -> lookupExTy (ExCons Γ) (S x) (ty_shift A 0)
| l_exty_SExTy  : forall Γ A B x, lookupExTy Γ x A -> lookupExTy (ExTyCons Γ B) (S x) (ty_shift A 0)
| l_exty_STm    : forall Γ A B x, lookupExTy Γ x A -> lookupExTy (TmCons Γ B) x A.

(* lookup an entry in subtyping env: solution (simpler ver.) *)
Inductive lookupExTy' : Env -> nat -> Prop :=
| l_exty'_Z      : forall Γ A, lookupExTy' (ExTyCons Γ A) 0
| l_exty'_STy    : forall Γ x, lookupExTy' Γ x -> lookupExTy' (TyCons Γ) (S x)
| l_exty'_STEx   : forall Γ x, lookupExTy' Γ x -> lookupExTy' (ExCons Γ) (S x)
| l_exty'_STExTy : forall Γ B x, lookupExTy' Γ x -> lookupExTy' (ExTyCons Γ B) (S x)
| l_exty'_STm    : forall Γ A x, lookupExTy' Γ x -> lookupExTy' (TmCons Γ A) x.

(* A [k / T] *)
Fixpoint subst (A : Typ) (k : nat) (T : Typ) : Typ :=
  match A with
  | Int => Int
  | TVar X => match lt_eq_lt_dec X k with
             | inleft (left _) => TVar X
             | inleft (right _) => T
             | inright _ => TVar (X - 1)
             end
  | Arr A B => Arr (subst A k T) (subst B k T)
  | All A => All (subst A (S k) (ty_shift T 0))
  end.

(* a ground type, just like system-f types *)
Inductive GroundTyp : Env -> Typ -> Prop :=
| r_int : forall Γ, GroundTyp Γ Int
| r_var : forall Γ n,
    lookupTy Γ n ->
    GroundTyp Γ (TVar n)
| r_arr : forall Γ A B,
    GroundTyp Γ A ->
    GroundTyp Γ B ->
    GroundTyp Γ (Arr A B)
| r_all : forall Γ A,
    GroundTyp (TyCons Γ) A ->
    GroundTyp Γ (All A).

Inductive TGround : Env -> Prop :=
| treg_Z : TGround EnvEmpty
| treg_STm : forall Γ A,
    TGround Γ ->
    GroundTyp Γ A ->
    TGround (TmCons Γ A)
| treg_STy : forall Γ,
    TGround Γ ->
    TGround (TyCons Γ)
| treg_SEx : forall Γ,
    TGround Γ ->
    TGround (ExCons Γ)
| treg_SExTy : forall Γ A,
    TGround Γ ->
    GroundTyp Γ A ->
    TGround (ExTyCons Γ A).

Inductive SGround : Env -> Prop :=
| sreg_Z : forall Γ, TGround Γ -> SGround (SepCons Γ)
| sreg_STy : forall Δ,
    SGround Δ ->
    SGround (TyCons Δ)
| sreg_SEx : forall Δ,
    SGround Δ ->
    SGround (ExCons Δ)
| sreg_SExTy : forall Δ A,
    SGround Δ ->
    GroundTyp Δ A ->
    SGround (ExTyCons Δ A).

(* replace entry ^a with a solution ^a=A in an environment *)
Inductive substEnv : Typ -> nat -> Env -> Env -> Prop :=
| se_ExZ : forall A A' Γ,
    A' = ty_shift A 0 ->
    GroundTyp Γ A ->
    SGround Γ ->
    substEnv A' 0 (ExCons Γ) (ExTyCons Γ A)
| se_ExS : forall k A A' Γ Γ',
    substEnv A k Γ Γ' ->
    A' = ty_shift A 0 ->
    substEnv A' (S k) (ExCons Γ) (ExCons Γ')
| se_TyS : forall k A A' Γ Γ',
    substEnv A k Γ Γ' ->
    A' = ty_shift A 0 ->
    substEnv A' (S k) (TyCons Γ) (TyCons Γ')
| se_ExTyS : forall k A A' B Γ Γ',
    substEnv A k Γ Γ' ->
    A' = ty_shift A 0 ->
    GroundTyp Γ B ->
    substEnv A' (S k) (ExTyCons Γ B) (ExTyCons Γ' B).

Inductive Polar : Set :=
| Pos : Polar
| Neg : Polar.

Definition neg (p : Polar) : Polar :=
  match p with
  | Pos => Neg
  | Neg => Pos
  end.

Inductive open : Env -> Typ -> Prop :=
| o_var_ex : forall Δ x,
    lookupEx Δ x ->
    open Δ (TVar x)
| o_arr_l : forall Δ A B,
    open Δ A ->
    open Δ (Arr A B)
| o_arr_r : forall Δ A B,
    open Δ B ->
    open Δ (Arr A B)
| o_all : forall Δ A,
    open (TyCons Δ) A ->
    open Δ (All A).

Inductive close : Env -> Typ -> Prop :=
| c_int : forall Δ, close Δ Int
| c_var_ty : forall Δ x,
    lookupTy Δ x ->
    close Δ (TVar x)
| c_var_exty : forall Δ x,
    lookupExTy' Δ x ->
    close Δ (TVar x) 
| c_arr : forall Δ A B,
    close Δ A ->
    close Δ B ->
    close Δ (Arr A B)
| c_all : forall Δ A,
    close (TyCons Δ) A ->
    close Δ (All A).
