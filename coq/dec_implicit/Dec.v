Require Import Syntax.
Require Import Algo.
Require Import Lia.
From Hammer Require Import Tactics.
Require Import Coq.Program.Equality.

Fixpoint tm_size (e : Trm) : nat :=
  match e with
  | Lit _ => 1
  | Var _ => 1
  | Lam e' => 1 + tm_size e'
  | App e1 e2 => 2 + tm_size e1 + tm_size e2
  | Ann e' _ => 1 + tm_size e'
  | TLam e' => 1 + tm_size e'
  | TApp e' _ => 1 + tm_size e'
  end.

Fixpoint ctx_size (Σ : Context) : nat :=
  match Σ with
  | CtxEmpty => 0
  | CtxTyp _ => 0
  | CtxTrm e Σ' => 1 + tm_size e + ctx_size Σ'
  | CtxTApp _ Σ' => 1 + ctx_size Σ'
  end.

Fixpoint ty_size (A : Typ) : nat :=
  match A with
  | Int => 1
  | TVar _ => 1
  | Arr A1 A2 => 1 + ty_size A1 + ty_size A2
  | All A' => 1 + ty_size A'
  end.

Lemma dec_CtxEmpty Σ :
  {Σ = CtxEmpty} + {NonEmpty Σ}.
Proof. sauto lq: on. Qed.

Lemma dec_sub : forall Δ A p B,
  {Ω | sub Δ A p B Ω} + {~ exists Ω, sub Δ A p B Ω}.
Admitted.

Lemma dec_ty_sub_ctx' : forall n,
  (forall Γ Σ e, tm_size e + ctx_size Σ < n ->
    {A | ty Γ Σ e A} + {~ exists A, ty Γ Σ e A}) *
  (forall Δ A Σ, ctx_size Σ < n ->
    {Δ' : Env & {A' : Typ & sub_ctx Δ A Σ Δ' A'}} + {~ exists Δ' A', sub_ctx Δ A Σ Δ' A'}).
Admitted.
