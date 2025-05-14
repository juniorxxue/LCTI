Require Import Syntax.

Inductive sub : env -> type -> polar -> type -> env -> Prop :=
| subInt : forall {Δ p},
    SRegularEnv Δ ->
    sub Δ Int p Int Δ
| subTVar : forall {Δ p x},
    SRegularEnv Δ ->
    lookupTyVar Δ x ->
    sub Δ (TVar x) p (TVar x) Δ
| subExL : forall {Δ Ψ x A},
    substEnv A x Δ Ψ ->
    sub Ψ (TVar x) Pos A Ψ
| subExR : forall {Δ Ψ x A},
    substEnv A x Δ Ψ ->
    sub Ψ A Neg (TVar x) Ψ
| subExTypL : forall {Δ x A},
    SRegularEnv Δ ->
    lookupExTyp Δ x A ->
    sub Δ (TVar x) Pos A Δ
| subExTypR : forall {Δ x A},
    SRegularEnv Δ ->
    lookupExTyp Δ x A ->
    sub Δ A Neg (TVar x) Δ
| subArr : forall {Δ Ω Ψ p x A B C D},
    sub Δ C (neg p) A Ω ->
    sub Ω B p D Ψ ->
    sub Δ (Arr A B) x (Arr C D) Ψ
| subFall : forall {Δ Ψ p A B},
    sub (TyCons Δ) A p B (TyCons Ψ) ->
    sub Δ (Fall A) p (Fall B) Ψ
.

Inductive ty : env -> context -> term -> type -> Prop :=
| tyLit : forall {Γ n},
    TRegularEnv Γ ->
    ty Γ ctxEmpty (Lit n) Int
| tyVar : forall {Γ x A},
    TRegularEnv Γ ->
    lookup Γ x A ->
    ty Γ ctxEmpty (Var x) A
| tyAnn : forall {Γ e A B},
    ty Γ (ctxType A) e B ->
    ty Γ ctxEmpty (Ann e A) A
| tyApp : forall {Γ Σ e1 e2 A B},
    ty Γ (ctxTerm e2 Σ) e1 (Arr A B) ->
    ty Γ Σ (App e1 e2) B
| tyLam1 : forall {Γ A B C e},
    ty (TBCons Γ A) (ctxType B) e C ->
    ty Γ (ctxType (Arr A B)) (Lam e) (Arr A C)
| tyLam2 : forall {Γ Σ A B e e2},
    ty Γ ctxEmpty e2 A ->
    ty (TBCons Γ A) (ctxtmshift Σ 0) e B ->
    ty Γ (ctxTerm e2 Σ) (Lam e) (Arr A B)
| tySub : forall {Γ Σ g A B},
    ty Γ ctxEmpty g A ->
    nonEmpty Σ ->
    genericConsumer g ->
    (* sub Γ A Σ -> *)
    ty Γ Σ g B
| tyTAbs : forall {Γ e A},
    ty (TyCons Γ) ctxEmpty e A ->
    ty Γ ctxEmpty (TLam e) (Fall A)
| tyTApp : forall {Γ Σ e A B B'},
    ty Γ (ctxTApp A Σ) e (Fall B) ->
    B' = subst B 0 A ->
    ty Γ Σ (TApp e A) B'.
  
Inductive grd_typ : env -> type -> type -> Prop :=
| grd_typInt : forall Δ, grd_typ Δ Int Int
| grd_typExTyp : forall Δ x A,
    lookupExTyp Δ x A ->
    grd_typ Δ (TVar x) A
| grd_typTVar : forall Δ x,
    lookupTyVar Δ x ->
    grd_typ Δ (TVar x) (TVar x)
| grd_typArr : forall Δ A B A' B',
    grd_typ Δ A A' ->
    grd_typ Δ B B' ->
    grd_typ Δ (Arr A B) (Arr A' B')
| grd_typFall : forall Δ A A',
    grd_typ (TyCons Δ) A A' ->
    grd_typ Δ (Fall A) (Fall A').

Fixpoint rm_sep (Γ : env) : env :=
  match Γ with
  | Empty => Empty
  | TBCons Γ' A => TBCons (rm_sep Γ') A
  | ExCons Γ' => ExCons (rm_sep Γ')
  | TyCons Γ' => TyCons (rm_sep Γ')
  | ExTypCons Γ' A => ExTypCons (rm_sep Γ') A
  | SepCons Γ' => rm_sep Γ'
  end.

Inductive sub_ctx : env -> type -> context -> env -> type -> Prop :=
| sub_ctxEmpty : forall {Δ A A'},
    SRegularEnv Δ ->
    close Δ A ->
    grd_typ Δ A A' ->
    sub_ctx Δ A ctxEmpty Δ A'
| sub_ctxType : forall {Δ A B Ψ},
    sub Δ A Pos B Ψ ->
    sub_ctx Δ A (ctxType B) Ψ B
| sub_ctxTermClose : forall {Δ A B Σ Ψ e A' A'' D},
    close Δ A ->
    grd_typ Δ A A' ->
    ty (rm_sep Δ) (ctxType A') e A'' ->
    sub_ctx Δ B Σ Ψ D ->
    sub_ctx Δ (Arr A B) (ctxTerm e Σ) Ψ (Arr A'' D)
| sub_ctxTermOpen : forall {Δ A B e Σ Ψ C D Ω},
    open Δ A ->
    ty (rm_sep Δ) ctxEmpty e C ->
    sub Δ C Neg A Ω ->
    sub_ctx Ω B Σ Ψ D ->
    sub_ctx Δ (Arr A B) (ctxTerm e Σ) Ψ (Arr C D)
| sub_ctxAllL : forall {Δ A e Σ Ψ B C D},
    sub_ctx (ExCons Δ) A (ctxTerm (tmtyshift e 0) (ctxtyshift Σ 0)) (ExTypCons Ψ B) (Arr (tyshift C 0) (tyshift D 0)) ->
    sub_ctx Δ (Fall A) (ctxTerm e Σ) Ψ (Arr C D)
| sub_ctxTApp : forall {Δ A B Σ Ψ C},
    sub_ctx (ExTypCons Δ B) A (ctxtyshift Σ 0) (ExTypCons Ψ B) C ->
    sub_ctx Δ (Fall A) (ctxTApp B Σ) Ψ (Fall C)
.
