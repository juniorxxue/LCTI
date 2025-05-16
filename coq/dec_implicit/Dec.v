Require Import Syntax.
Require Import Algo.
Require Import Lia.
From Hammer Require Import Tactics.
Require Import Coq.Program.Equality.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.PeanoNat.

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

Lemma eq_dec_ty : forall (A B : Typ),
  {A = B} + {A <> B}.
Proof.  decide equality. decide equality. Qed.

Lemma dec_ty_unshift : forall A k,
  {A' | A = ty_shift A' k} + {~ exists A', A = ty_shift A' k}.
Proof.
  intro A; induction A; intro k.
  - left. exists Int. sfirstorder.
  - destruct (lt_dec n k) as [Hlt | Hlt].
    + left. exists (TVar n). simpl. unfold punchIn. sauto l: on.
    + assert (Hle: k <= n) by lia.
      destruct n.
      * right. intros [A' Heq].
        destruct A'; try sfirstorder.
        sauto q: on.
      * destruct (le_dec k n) as [Hle' | Hle'].
        -- left. exists (TVar n). simpl. unfold punchIn. sauto l: on.
        -- assert (Heq: k = S n) by lia. subst. 
           right. intros [A' Heq].
           destruct A'; try sfirstorder.
           dependent destruction Heq. unfold punchIn in *.
           destruct (Nat.leb (S n) n0) eqn:Hle''; unfold punchIn in *; hauto lqb: on.
  - specialize (IHA1 k). specialize (IHA2 k).
    destruct IHA1 as [[A1' Heq1] | Hneq1]; destruct IHA2 as [[A2' Heq2] | Hneq2]; subst.
    + left. exists (Arr A1' A2'). sfirstorder.
    + right. intros [A' Heq]. destruct A'; try sfirstorder.
    + right. intros [A' Heq]. destruct A'; try sfirstorder.
    + right. intros [A' Heq]. destruct A'; try sfirstorder.
  - specialize (IHA (S k)). destruct IHA as [[A' Heq] | Hneq]; subst.
    + left. exists (All A'). sfirstorder.
    + right. intros [A'' Heq]. destruct A''; try sfirstorder.
Qed.

Lemma ty_unshift_det : forall B k A1 A2,
  B = ty_shift A1 k -> B = ty_shift A2 k -> A1 = A2.
Proof.
  intro B. induction B; intros k A1 A2 Heq1 Heq2;
    destruct A1; destruct A2; try sfirstorder; simpl in *.
  - unfold punchIn in *.
    destruct (le_dec k n0); destruct (le_dec k n1).
    sauto l: on. hauto l: on. sauto lq: on. hauto q: on.
  - hauto lq: on rew: off.
  - hauto q: on.
Qed.

(* Lemma lookupTm : forall Γ x,
  {A | lookupTm Γ x A} + {~ exists A, lookupTm Γ x A}.
Proof.
  intro Γ. induction Γ; intro x.
  best.  *)

Lemma dec_lookupTy : forall Γ x,
  {lookupTy Γ x} + {~ lookupTy Γ x}.
Proof.
  intro Γ. induction Γ; intro x.
  - sauto lq: on.
  - specialize (IHΓ x). sauto lq: on.
  - destruct x; try specialize (IHΓ x); sauto lq: on.
  - destruct x; try specialize (IHΓ x); sauto lq: on.
  - destruct x; try specialize (IHΓ x); sauto lq: on.
  - specialize (IHΓ x). sauto lq: on.
Qed.

Lemma dec_lookupEx : forall Δ x,
  {lookupEx Δ x} + {~ lookupEx Δ x}.
Proof.
  intro Δ. induction Δ; intro x.
  - sauto lq: on.
  - specialize (IHΔ x). sauto lq: on.
  - destruct x; try specialize (IHΔ x); sauto lq: on.
  - destruct x; try specialize (IHΔ x); sauto lq: on.
  - destruct x; try specialize (IHΔ x); sauto lq: on.
  - specialize (IHΔ x). sauto lq: on.
Qed.

Lemma dec_lookupExTyO : forall Δ x A,
  {lookupExTy Δ x A} + {~ lookupExTy Δ x A}.
Proof.
  intro Δ. induction Δ; intros x A.
  - sauto lq: on.
  - destruct (dec_ty_unshift A 0) as [[A' Heq] | Hneq]; subst.
    + specialize (IHΔ x A'). sauto q: on use: ty_unshift_det.
    + sauto lq: on.
  - destruct x. sauto lq: on.
    destruct (dec_ty_unshift A 0) as [[A' Heq] | Hneq]; subst.
    + specialize (IHΔ x A'). sauto q: on use: ty_unshift_det.
    + sauto lq: on.
  - destruct x. sauto lq: on.
    destruct (dec_ty_unshift A 0) as [[A' Heq] | Hneq]; subst.
    + specialize (IHΔ x A'). sauto q: on use: ty_unshift_det.
    + sauto lq: on.
  - destruct x.
    destruct (eq_dec_ty A (ty_shift t 0)); subst; sauto lq: on.
    destruct (dec_ty_unshift A 0) as [[A' Heq] | Hneq]; subst.
    + specialize (IHΔ x A'). sauto q: on use: ty_unshift_det.
    + sauto lq: on.
  - sauto lq: on.
Qed.

Lemma dec_lookupExTy : forall Δ x,
  {A | lookupExTy Δ x A} + {~ exists A, lookupExTy Δ x A}.
Proof.
  intro Δ. induction Δ; intros x.
  - sauto lq: on.
  - destruct (IHΔ x) as [[A' Heq] | Hneq]; sauto lq: on.
  - destruct x. sauto lq: on.
    destruct (IHΔ x) as [[A' Heq] | Hneq]; sauto lq: on.
  - destruct x. sauto lq: on.
    destruct (IHΔ x) as [[A' Heq] | Hneq]; sauto lq: on.
  - destruct x. sauto lq: on.
    destruct (IHΔ x) as [[A' Heq] | Hneq]; sauto lq: on.
  - destruct x. sauto lq: on.
    destruct (IHΔ x) as [[A' Heq] | Hneq]; sauto lq: on.
Qed.

Lemma dec_RegularTyp : forall Γ A,
  {RegularTyp Γ A} + {~ RegularTyp Γ A}.
Proof.
  intros Γ A. generalize dependent Γ.
  induction A; intro Γ; try sfirstorder.
  - destruct (dec_lookupTy Γ n); sauto lq: on.
  - specialize (IHA1 Γ). specialize (IHA2 Γ). sauto q: on.
  - specialize (IHA (TyCons Γ)). sauto q: on.
Qed.

Lemma dec_Regular : forall Γ,
  {Regular Γ} + {~ Regular Γ}.
Proof.
  intro Γ. induction Γ; try sfirstorder.
  - destruct (dec_RegularTyp Γ t); sauto lq: on.
  - sauto lq: on.
  - sauto lq: on.
  - destruct (dec_RegularTyp Γ t); sauto lq: on.
  - sauto lq: on.
Qed.

Lemma dec_TRegular : forall Δ,
  {TRegular Δ} + {~ TRegular Δ}.
Proof.
  intro Δ. induction Δ; try sfirstorder.
  - destruct (dec_RegularTyp Δ t); sauto lq: on.
  - sauto lq: on.
  - sauto lq: on.
  - destruct (dec_RegularTyp Δ t); sauto lq: on.
  - sauto lq: on.
Qed.

Lemma dec_SRegular : forall Δ,
  {SRegular Δ} + {~ SRegular Δ}.
Proof.
  intro Δ. induction Δ.
  1 - 4 : sauto lq: on.
  - destruct (dec_RegularTyp Δ t); sauto lq: on.
  - destruct (dec_TRegular Δ); sauto lq: on.
Qed.

Lemma dec_substEnv : forall A x Γ,
  {Γ' | substEnv A x Γ Γ'} + {~ exists Γ', substEnv A x Γ Γ'}.
Proof.
  intros A x Γ. generalize dependent x. generalize dependent A.
  induction Γ; intros A x.
  - sauto lq: on.
  - sauto lq: on.
  - destruct x.
    + destruct (dec_SRegular Γ). 2 : sauto lq: on.
      destruct (dec_ty_unshift A 0) as [[A' Heq] | Hneq]; subst. 2 : sauto lq: on.
      destruct (dec_RegularTyp Γ A'); sauto lq: on use: ty_unshift_det.
    + destruct (dec_ty_unshift A 0) as [[A' Heq] | Hneq]; subst.
      * specialize (IHΓ A' x). sauto q: on use: ty_unshift_det.
      * sauto lq: on rew: off use: ty_unshift_det.
  - destruct x. sauto lq: on.
    destruct (dec_ty_unshift A 0) as [[A' Heq] | Hneq]; subst.
    + specialize (IHΓ A' x). sauto q: on use: ty_unshift_det.
    + sauto lq: on rew: off use: ty_unshift_det.
  - destruct x. sauto lq: on.
    destruct (dec_ty_unshift A 0) as [[A' Heq] | Hneq]; subst. 2 : sauto lq: on.
    destruct (dec_RegularTyp Γ t). 2 : sauto lq: on.
    specialize (IHΓ A' x). destruct IHΓ.
    + sauto lq: on use: ty_unshift_det.
    + right. intros [Γ' Heq]. sauto lq: on rew: off use: ty_unshift_det.
  - sauto lq: on.
Qed.


Lemma lookupTy_Ex : forall Δ x,
  lookupTy Δ x -> lookupEx Δ x -> False.
Proof. intro Δ. induction Δ; intros x Hty Hex; sauto lq: on. Qed.

Lemma lookupTy_ExTy : forall Δ x A,
  lookupTy Δ x -> lookupExTy Δ x A -> False.
Proof. intro Δ. induction Δ; intros x A Hty Hex; sauto lq: on. Qed.

Lemma lookupEx_ExTy : forall Δ x A,
  lookupEx Δ x -> lookupExTy Δ x A -> False.
Proof. intro Δ. induction Δ; intros x A Hex Hexty; sauto lq: on. Qed.

Lemma substEnv_Ex : forall Δ A x Ψ,
  substEnv A x Δ Ψ -> lookupEx Δ x.
Proof. intro Δ. induction Δ; intros A x Ψ Hsubst; sauto lq: on. Qed.

Definition NotVar (A : Typ) : Prop :=
  match A with
  | Int => True
  | TVar _ => False
  | Arr A1 A2 => True
  | All A' => True
  end.

Lemma substEnv_det : forall Δ A x Ψ1 Ψ2,
  substEnv A x Δ Ψ1 -> substEnv A x Δ Ψ2 -> Ψ1 = Ψ2.
Proof.
  intros Δ A x Ψ1 Ψ2 Hs1 Hs2. generalize dependent Ψ2.
  induction Hs1; intros * Hs2; sauto lq: on rew: off use: ty_unshift_det.
Qed.

Lemma sub_det : forall Δ A p B Ω1 Ω2,
  sub Δ A p B Ω1 -> sub Δ A p B Ω2 -> Ω1 = Ω2.
Proof.
  intros Δ A p B Ω1 Ω2 Hsub1 Hsub2. generalize dependent Ω2.
  induction Hsub1; intros * Hsub2;
  sauto l: on use: lookupTy_Ex, lookupTy_ExTy, lookupEx_ExTy, substEnv_Ex, substEnv_det.
Qed.

Lemma dec_sub' : forall n Δ A p B,
  ty_size A + ty_size B < n ->
  {Ω | sub Δ A p B Ω} + {~ exists Ω, sub Δ A p B Ω}.
Proof.
  intro n. induction n; intros Δ A p B Hlt; try lia.
  assert (TVarL: forall x, A = TVar x -> NotVar B -> {Ω | sub Δ A p B Ω} + {~ exists Ω, sub Δ A p B Ω}).
  { intros x Heq Hnvar. subst.
    destruct p. 2 : sauto lq: on.
    destruct (dec_substEnv B x Δ) as [[Δ' Hsubst] | Hsubst]. sauto lq: on.
    destruct (dec_SRegular Δ). 2 : sauto lq: on.
    destruct (dec_lookupExTyO Δ x B); sauto lq: on. }
  assert (TVarR: forall x, NotVar A -> B = TVar x -> {Ω | sub Δ A p B Ω} + {~ exists Ω, sub Δ A p B Ω}).
  { intros x Hnvar Heq. subst.
    destruct p. sauto lq: on.
    destruct (dec_substEnv A x Δ) as [[Δ' Hsubst] | Hsubst]. sauto lq: on.
    destruct (dec_SRegular Δ). 2 : sauto lq: on.
    destruct (dec_lookupExTyO Δ x A); sauto lq: on. }
  destruct A.
  - destruct B.
    + destruct (dec_SRegular Δ); sauto lq: on.
    + hauto lq: on use: TVarR.
    + sauto lq: on.
    + sauto lq: on.
  - clear TVarR. destruct B.
    + hauto lq: on use: TVarL. 
    + clear TVarL. destruct (dec_lookupTy Δ n0).
      * destruct (dec_lookupTy Δ n1).
        -- destruct (Nat.eq_dec n0 n1); subst.
           ++ destruct (dec_SRegular Δ). sauto lq: on.
              sauto lq: on use: lookupTy_Ex, lookupTy_ExTy, substEnv_Ex.
           ++ sauto lq: on use: lookupTy_Ex, lookupTy_ExTy, substEnv_Ex.
        -- destruct p. sauto lq: on use: lookupTy_Ex, lookupTy_ExTy, substEnv_Ex.
           destruct (dec_substEnv (TVar n0) n1 Δ) as [[Δ' Hsubst] | Hsubst]. sauto lq: on.
           destruct (dec_lookupExTyO Δ n1 (TVar n0)).
           ++ destruct (dec_SRegular Δ). sauto lq: on.
              sauto lq: on use: lookupTy_Ex, lookupTy_ExTy, substEnv_Ex.
           ++ sauto lq: on use: lookupTy_Ex, lookupTy_ExTy, substEnv_Ex.
      * destruct (dec_substEnv (TVar n1) n0 Δ) as [[Δ' Hsubst] | Hsubst].
        -- destruct p. sauto lq: on.
           destruct (dec_substEnv (TVar n0) n1 Δ) as [[Δ'' Hsubst'] | Hsubst']. sauto lq: on.
           destruct (dec_SRegular Δ). 2 : sauto lq: on.
           destruct (dec_lookupExTyO Δ n1 (TVar n0)). sauto lq: on.
           sauto lq: on use: lookupTy_Ex, lookupTy_ExTy, substEnv_Ex.
        -- destruct (dec_lookupExTyO Δ n0 (TVar n1)).
           ++ destruct (dec_SRegular Δ).
              ** destruct p. sauto lq: on use: lookupTy_Ex, lookupTy_ExTy, substEnv_Ex.
                 destruct (dec_lookupTy Δ n1). sauto lq: on use: lookupTy_Ex, lookupTy_ExTy, substEnv_Ex.
                 destruct (dec_substEnv (TVar n0) n1 Δ) as [[Δ' Hsubst'] | Hsubst']. sauto lq: on.
                 destruct (dec_lookupExTyO Δ n1 (TVar n0)). sauto lq: on.
                 sauto lq: on use: lookupTy_Ex, lookupTy_ExTy, substEnv_Ex.
              ** destruct p. sauto lq: on.
                 destruct (dec_lookupTy Δ n1). sauto lq: on use: lookupTy_Ex, lookupTy_ExTy, substEnv_Ex.
                 destruct (dec_substEnv (TVar n0) n1 Δ) as [[Δ' Hsubst'] | Hsubst']. sauto lq: on.
                 destruct (dec_lookupExTyO Δ n1 (TVar n0)). sauto lq: on.
                 sauto lq: on use: lookupTy_Ex, lookupTy_ExTy, substEnv_Ex.
           ++ destruct (dec_substEnv (TVar n0) n1 Δ) as [[Δ' Hsubst'] | Hsubst'].
              destruct p; sauto lq: on.
              destruct (dec_lookupExTyO Δ n1 (TVar n0)).
              ** destruct p. sauto lq: on.
                 destruct (dec_SRegular Δ). sauto lq: on.
                 sauto lq: on use: lookupTy_Ex, lookupTy_ExTy, substEnv_Ex.
              ** sauto lq: on use: lookupTy_Ex, lookupTy_ExTy, substEnv_Ex.
    + hauto lq: on use: TVarL.
    + hauto lq: on use: TVarL.
  - destruct B.
    + sauto lq: on.
    + hauto lq: on use: TVarR.
    + clear TVarL TVarR. simpl in *.
      assert (Hlt1: ty_size B1 + ty_size A1 < n) by lia.
      assert (Hlt2: ty_size A2 + ty_size B2 < n) by lia.
      eapply IHn with (Δ := Δ) (p := neg p) in Hlt1 as IHn1.
      destruct IHn1 as [[Ω Hsub1] | Hneg1].
      * eapply IHn with (Δ := Ω) (p := p) in Hlt2 as IHn2.
        destruct IHn2 as [[Ψ Hsub2] | Hneg2].
        -- sauto lq: on.
        -- right. intros [Ψ' Hc]. dependent destruction Hc.
           eapply sub_det in Hsub1; eauto. subst. sfirstorder.
      * sauto lq: on.
    + sauto lq: on.
  - destruct B.
    + sauto lq: on.
    + hauto lq: on use: TVarR.
    + sauto lq: on.
    + clear TVarL TVarR. simpl in *.
      assert (Hlt': ty_size A + ty_size B < n) by lia.
      eapply IHn with (Δ := TyCons Δ) (p := p) in Hlt' as IHn1.
      destruct IHn1 as [[Ω Hsub] | Hneg].
      * destruct Ω; try solve [right; intros [Ω' Hc]; dependent destruction Hc;
          eapply sub_det in Hsub; eauto; subst; sfirstorder].
        sauto lq: on.
      * sauto lq: on.
Qed.

Theorem dec_sub : forall Δ A p B,
  {Ω | sub Δ A p B Ω} + {~ exists Ω, sub Δ A p B Ω}.
Proof. intros. eapply dec_sub'; eauto. Qed.

Lemma dec_ty_sub_ctx' : forall n,
  (forall Γ Σ e, tm_size e + ctx_size Σ < n ->
    {A | ty Γ Σ e A} + {~ exists A, ty Γ Σ e A}) *
  (forall Δ A Σ, ctx_size Σ < n ->
    {Δ' : Env & {A' : Typ & sub_ctx Δ A Σ Δ' A'}} + {~ exists Δ' A', sub_ctx Δ A Σ Δ' A'}).
Admitted.

Theorem dec_ty : forall Γ Σ e,
  {A | ty Γ Σ e A} + {~ exists A, ty Γ Σ e A}.
Proof. hauto lq: on use: dec_ty_sub_ctx'. Qed.

Theorem dec_sub_ctx : forall Δ A Σ,
  {Δ' : Env & {A' : Typ & sub_ctx Δ A Σ Δ' A'}} + {~ exists Δ' A', sub_ctx Δ A Σ Δ' A'}.
Proof. hauto lq: on use: dec_ty_sub_ctx'. Qed.
