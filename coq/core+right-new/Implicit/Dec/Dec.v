Require Import Syntax.
Require Import Algo.
Require Import Lia.
From Hammer Require Import Tactics.
From Coq Require Import Extraction.
Require Import Coq.Program.Equality.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.PeanoNat.

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

Lemma ty_unshift_tm_det : forall e' k e1 e2,
  e' = ty_shift_tm e1 k -> e' = ty_shift_tm e2 k -> e1 = e2.
Proof.
  intro e'. induction e'; intros k e1 e2 Heq1 Heq2;
    destruct e1; destruct e2; try sfirstorder; simpl in *;
    sauto lq: on rew: off use: ty_unshift_det.
Qed.

Lemma ty_unshift_ctx_det : forall Σ k Σ1 Σ2,
  Σ = ty_shift_ctx Σ1 k -> Σ = ty_shift_ctx Σ2 k -> Σ1 = Σ2.
Proof.
  intro Σ. induction Σ; intros k Σ1 Σ2 Heq1 Heq2;
    destruct Σ1; destruct Σ2; try sfirstorder; simpl in *;
    hauto lq: on rew: off use: ty_unshift_det, ty_unshift_tm_det.
Qed.

Lemma dec_lookupTm : forall Δ x,
  {A | lookupTm Δ x A} + {~ exists A, lookupTm Δ x A}.
Proof.
  intro Δ. induction Δ; intros x.
  3 - 6 : destruct (IHΔ x) as [[A' Heq] | Hneq]; sauto lq: on.
  - sauto lq: on.
  - destruct x. sauto lq: on.
    destruct (IHΔ x) as [[A' Heq] | Hneq]; sauto lq: on.
Qed.

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
  - specialize (IHΔ x A). sauto lq: on.
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

Lemma dec_lookupExTy' : forall Δ x,
  {lookupExTy' Δ x} + {~ lookupExTy' Δ x}.
Proof.
  intro Δ. induction Δ; intro x.
  - sauto lq: on.
  - specialize (IHΔ x). sauto lq: on rew: off.
  - destruct x. sauto lq: on.
    destruct (IHΔ x) as [Hlk | Hnlk]; sauto lq: on.
  - destruct x. sauto lq: on.
    destruct (IHΔ x) as [Hlk | Hnlk]; sauto lq: on.
  - destruct x. sauto lq: on.
    destruct (IHΔ x) as [Hlk | Hnlk]; sauto lq: on.
  - destruct x. sauto lq: on.
    destruct (IHΔ x) as [Hlk | Hnlk]; sauto lq: on.
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
           ++ sauto l: on use: lookupTy_Ex, lookupTy_ExTy, substEnv_Ex.
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
      eapply IHn with (Δ := Δ) (p := p) in Hlt2 as IHn2.
      destruct IHn2 as [[Ω Hsub2] | Hneg2].
      * eapply IHn with (Δ := Ω) (p := neg p) in Hlt1 as IHn1.
        destruct IHn1 as [[Ψ Hsub1] | Hneg1].
        -- sauto lq: on.
        -- right. intros [Ψ' Hc]. dependent destruction Hc.
           eapply sub_det in Hsub2; eauto. subst. sfirstorder.
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

Fixpoint tm_size (e : Trm) : nat :=
  match e with
  | Lit _ => 1
  | Var _ => 1
  | Lam e' => 1 + tm_size e'
  | App e1 e2 => 3 + tm_size e1 + tm_size e2
  | Ann e' _ => 2 + tm_size e'
  | TLam e' => 1 + tm_size e'
  | TApp e' _ => 2 + tm_size e'
  end.

Fixpoint ctx_size (Σ : Context) : nat :=
  match Σ with
  | CtxEmpty => 0
  | CtxTyp _ => 1
  | CtxTrm e Σ' => 2 + tm_size e + ctx_size Σ'
  | CtxTApp _ Σ' => 1 + ctx_size Σ'
  end.

Lemma NonEmpty_ctx_size_gt0 : forall Σ,
  NonEmpty Σ -> ctx_size Σ > 0.
Proof.
  intros Σ Hne. destruct Σ; simpl in *; try sfirstorder.
  sauto lq: on.
Qed. 

Lemma tm_size_gt0 : forall e, tm_size e > 0.
Proof. induction e; simpl; lia. Qed.

Lemma lookupExTy_det : forall Δ x A A',
  lookupExTy Δ x A -> lookupExTy Δ x A' -> A = A'.
Proof.
  intros Δ x A A' Hlookup Hlookup'. generalize dependent A'.
  induction Hlookup; intros * Hlookup'; dependent destruction Hlookup'; sfirstorder use: ty_unshift_det.
Qed.

Lemma grd_typ_det : forall Δ A A' A'',
  grd_typ Δ A A' -> grd_typ Δ A A'' -> A' = A''.
Proof.
  intros Δ A A' A'' Hgrd1 Hgrd2. generalize dependent A''.
  induction Hgrd1; intros * Hgrd2; dependent destruction Hgrd2;
    sfirstorder use: lookupExTy_det, lookupTy_ExTy.
Qed.

Lemma lookupExTy_lookupExTy' : forall Δ x A,
  lookupExTy Δ x A -> lookupExTy' Δ x.
Proof. intros Δ x A Hlk. induction Hlk; sauto lq: on. Qed.

Lemma lookupExTy'_lookupExTy : forall Δ x,
  lookupExTy' Δ x -> exists A, lookupExTy Δ x A.
Proof. intros Δ x Hlk. induction Hlk; sauto lq: on. Qed.

Lemma open_close_false : forall Δ A,
  open Δ A -> close Δ A -> False.
Proof.
  intros Δ A Hopen Hclose.
  induction Hopen; dependent destruction Hclose;
    sfirstorder use: lookupTy_Ex, lookupEx_ExTy, lookupExTy'_lookupExTy.
Qed.

Lemma lookupTm_det : forall Γ x A A',
  lookupTm Γ x A -> lookupTm Γ x A' -> A = A'.
Proof.
  intros Γ x A A' Hlk. generalize dependent A'.
  induction Hlk; intros * Hlk'; dependent destruction Hlk'; sfirstorder.
Qed.

Lemma tm_size_tm_shift : forall e k,
  tm_size (tm_shift e k) = tm_size e.
Proof. induction e; intros k; simpl in *; try lia; try sfirstorder. Qed.

Lemma tm_size_ty_shift_tm : forall e k,
  tm_size (ty_shift_tm e k) = tm_size e.
Proof. induction e; intros k; simpl in *; try lia; try sfirstorder. Qed.

Lemma ty_size_ty_shift : forall A k,
  ty_size (ty_shift A k) = ty_size A.
Proof. induction A; intros k; simpl in *; try lia; try sfirstorder. Qed.

Lemma ctx_size_tm_shift : forall Σ k,
  ctx_size (tm_shift_ctx Σ k) = ctx_size Σ.
Proof. induction Σ; intros k; simpl; try lia; try sfirstorder use: tm_size_tm_shift. Qed.

Lemma ctx_size_ty_shift : forall Σ k,
  ctx_size (ty_shift_ctx Σ k) = ctx_size Σ.
Proof. induction Σ; intros k; simpl; try lia; try sfirstorder use: tm_size_ty_shift_tm. Qed.

Lemma NonEmpty_false : NonEmpty CtxEmpty -> False.
Proof. sauto lq: on. Qed.

Lemma substEnv_lookupTy : forall A x y Γ Γ',
  substEnv A x Γ Γ' -> lookupTy Γ y -> lookupTy Γ' y.
Proof.
  intros * Hsubst Hlk. generalize dependent y.
  induction Hsubst; intros * Hlk; sauto lq: on.
Qed.

Lemma substEnv_RegularTyp : forall Γ B, RegularTyp Γ B ->
  forall A x Γ', substEnv A x Γ Γ' -> RegularTyp Γ' B.
Proof.
  intros Γ B Hreg. dependent induction Hreg;
  intros * Hsubst; sauto lq: on use: substEnv_lookupTy.
Qed.

Lemma substEnv_SRegular_in : forall A x Γ Γ',
  substEnv A x Γ Γ' -> SRegular Γ.
Proof.
  intros A x Γ Γ' Hsubst.
  dependent induction Hsubst; sauto lq: on rew: off.
Qed.

Lemma substEnv_SRegular_out : forall A x Γ Γ',
  substEnv A x Γ Γ' -> SRegular Γ'.
Proof.
  intros A x Γ Γ' Hsubst.
  dependent induction Hsubst;
    sauto lq: on rew: off use: substEnv_RegularTyp.
Qed.

Lemma sub_SRegular_in : forall Δ A p B Ω,
  sub Δ A p B Ω -> SRegular Δ.
Proof.
  intros Δ A p B Ω Hsub.
  dependent induction Hsub; try sfirstorder use: substEnv_SRegular_in.
  sauto lq: on.
Qed.

Lemma sub_SRegular_out : forall Δ A p B Ω,
  sub Δ A p B Ω -> SRegular Ω.
Proof.
  intros Δ A p B Ω Hsub.
  dependent induction Hsub; try sfirstorder use: substEnv_SRegular_out.
  sauto lq: on.
Qed.

Lemma RegularTyp_weaken_gen : forall Γ A,
  RegularTyp Γ A -> forall Γ', (forall x, lookupTy Γ x -> lookupTy Γ' x) -> RegularTyp Γ' A.
Proof.
  intros Γ A Hreg.
  dependent induction Hreg; intros Γ' Hlk; sauto lq: on.
Qed.

Lemma RegularTyp_weaken_TmCons : forall Γ A,
  RegularTyp Γ A -> forall B, RegularTyp (TmCons Γ B) A.
Proof.
  intros Γ A Hreg.
  dependent induction Hreg; intros;
    sauto lq: on rew: off use: RegularTyp_weaken_gen.
Qed.

Lemma RegularTyp_weaken_gen_shift : forall Γ A,
  RegularTyp Γ A -> forall Γ' k,
    (forall x, lookupTy Γ x -> if k <=? x then lookupTy Γ' (S x) else lookupTy Γ' x) ->
  RegularTyp Γ' (ty_shift A k).
Proof.
  intros Γ A Hreg.
  dependent induction Hreg; intros Γ' k Hlk;
    simpl; unfold punchIn; try sfirstorder.
  1 - 2 : sauto lq: on rew: off.
  - econstructor. eapply IHHreg. intros x Hlk'.
    dependent destruction Hlk'.
    sfirstorder. scrush.
Qed.

Lemma RegularTyp_weaken_TyCons : forall Γ A,
  RegularTyp Γ A -> RegularTyp (TyCons Γ) (ty_shift A 0).
Proof.
  intros Γ A Hreg.
  dependent induction Hreg; sauto use: RegularTyp_weaken_gen_shift.
Qed.

Lemma RegularTyp_weaken_ExCons : forall Γ A,
  RegularTyp Γ A -> RegularTyp (ExCons Γ) (ty_shift A 0).
Proof.
  intros Γ A Hreg.
  dependent induction Hreg; sauto use: RegularTyp_weaken_gen_shift.
Qed.

Lemma RegularTyp_weaken_ExTyCons : forall Γ A,
  RegularTyp Γ A -> forall B, RegularTyp (ExTyCons Γ B) (ty_shift A 0).
Proof.
  intros Γ A Hreg.
  dependent induction Hreg; sauto use: RegularTyp_weaken_gen_shift.
Qed.

Lemma TRegular_lookupTm_RegularTyp : forall x Γ A,
  TRegular Γ -> lookupTm Γ x A -> RegularTyp Γ A.
Proof. 
  intros * Hreg Hlk.
  dependent induction Hlk;
     sauto lq: on use: RegularTyp_weaken_TmCons, RegularTyp_weaken_TyCons,
                       RegularTyp_weaken_ExCons, RegularTyp_weaken_ExTyCons.
Qed.

Lemma SRegular_lookupExTy_RegularTyp : forall x Γ A,
  SRegular Γ -> lookupExTy Γ x A -> RegularTyp Γ A.
Proof. 
  intros * Hreg Hlk.
  dependent induction Hlk;
     sauto lq: on use: RegularTyp_weaken_TmCons, RegularTyp_weaken_TyCons,
                       RegularTyp_weaken_ExCons, RegularTyp_weaken_ExTyCons.
Qed.

Lemma ty_TRegular : forall Γ Σ e A, ty Γ Σ e A -> TRegular Γ.
Proof.
  intros Γ Σ e A Hty. dependent induction Hty; simpl in *;
    try sfirstorder; sauto lq: on.
Qed.

Lemma sub_ctx_SRegular_in : forall Δ A Σ Δ' B,
  sub_ctx Δ A Σ Δ' B -> SRegular Δ.
Proof.
  intros * Hsub. dependent induction Hsub;
    sauto lq: on rew: off use: sub_SRegular_in.
Qed.

Lemma sub_ctx_SRegular_out : forall Δ A Σ Δ' B,
  sub_ctx Δ A Σ Δ' B -> SRegular Δ'.
Proof.
  intros * Hsub. dependent induction Hsub;
    ecrush use: sub_SRegular_out.
Qed.

Lemma TRegularTyp_strengthen_TmCons : forall Γ A B,
  TRegular Γ -> RegularTyp (TmCons Γ B) A -> RegularTyp Γ A.
Proof. sauto lq: on use: RegularTyp_weaken_gen. Qed.

Lemma TRegularTyp_strengthen_SepCons : forall Γ A,
  TRegular Γ -> RegularTyp (SepCons Γ) A -> RegularTyp Γ A.
Proof. sauto lq: on use: RegularTyp_weaken_gen. Qed.

Lemma ty_sub_ctx_infs_det' : forall n,
  (forall Γ Σ e A A', tm_size e + ctx_size Σ < n ->
    ty Γ Σ e A -> ty Γ Σ e A' -> A = A') /\
  (forall Δ A Σ Δ1 Δ2 A1 A2, ctx_size Σ < n ->
    sub_ctx Δ A Σ Δ1 A1 -> sub_ctx Δ A Σ Δ2 A2 -> Δ1 = Δ2 /\ A1 = A2) /\
  (forall Γ Σ A1 A2, ctx_size Σ < n ->
    infs Γ Σ A1 -> infs Γ Σ A2 -> A1 = A2).
Proof.
  intro n. induction n. repeat split; try lia.
  destruct IHn as [IHty [IHsub IHinfs]]. split.
  - intros Γ Σ e A A' Hlt Hty1 Hty2. generalize dependent A'.
    dependent induction Hty1; intros; dependent destruction Hty2; simpl in *;
      try sfirstorder use: NonEmpty_false, lookupTm_det;
      try solve [eapply IHty in Hty1; eauto; simpl; try lia; sfirstorder].
    + rewrite ctx_size_tm_shift in *.
      eapply IHHty1_1 in Hty2_1; eauto; try lia. subst.
      eapply IHHty1_2 in Hty2_2; eauto; try lia. sfirstorder.
    + assert (Hlt': tm_size g < n). { eapply NonEmpty_ctx_size_gt0 in H. lia. }
      assert (Hlt'': ctx_size Σ < n). { specialize (tm_size_gt0 g). lia. }
      eapply IHty in Hty1; eauto; simpl; try lia. subst.
      eapply IHsub with (Δ1 := (Γ ⋈)) in H1; eauto; simpl; try lia. sfirstorder.
    + sauto lq: on rew: off.
    + sauto lq: on rew: off. 
  - split.
    + intros Δ A Σ Δ1 Δ2 A1 A2 Hlt Hsub1 Hsub2.
      generalize dependent A2. generalize dependent Δ2.
      dependent induction Hsub1; intros; dependent destruction Hsub2; simpl in *;
        try sfirstorder use: grd_typ_det, sub_det, open_close_false;
        try solve [try rewrite ctx_size_ty_shift in *; try rewrite tm_size_ty_shift_tm in *;
                  eapply IHHsub1 in Hsub2; try lia; sfirstorder use: ty_unshift_det].
      * eapply IHsub in Hsub1; eauto; simpl; try lia.
        destruct Hsub1 as [Heq1 Heq2]. subst.
        eapply grd_typ_det in H0; eauto. subst.
        eapply IHty in H1; eauto; simpl; try lia.
      * eapply IHsub in Hsub1; eauto; simpl; try lia.
        hauto lq: on rew: off use: open_close_false.
      * eapply IHsub in Hsub1; eauto; simpl; try lia.
        hauto lq: on rew: off use: open_close_false.
      * eapply IHsub in Hsub1; eauto; simpl; try lia.
        destruct Hsub1 as [Heq1 Heq2]. subst.
        eapply IHty in H0; eauto; simpl; try lia. subst.
        eapply sub_det in H1; eauto; simpl; try lia.
      * eapply lookupExTy_det in H; eauto. subst. sfirstorder.
      * sauto lq: on rew: off use: substEnv_Ex, lookupEx_ExTy.
      * eapply lookupExTy_det in H; eauto. subst. sfirstorder.
      * sauto lq: on rew: off use: substEnv_Ex, lookupEx_ExTy.
      * dependent destruction H. dependent destruction H2.
        eapply IHty in H; eauto; simpl; try lia. subst.
        eapply IHinfs in H0; eauto; simpl; try lia. subst.
        eapply substEnv_det in H1; eauto; simpl; try lia.
    + intros Γ Σ A1 A2 Hlt Hinf1 Hinf2.
      generalize dependent A2.
      dependent induction Hinf1; intros; dependent destruction Hinf2; simpl in *; try sfirstorder.
      eapply IHty in H; eauto; simpl; try lia. subst.
      eapply IHinfs in Hinf1; eauto; simpl; try lia. scongruence.
Qed.

Lemma ty_det : forall Γ Σ e A A', ty Γ Σ e A -> ty Γ Σ e A' -> A = A'.
Proof. qauto l: on use: ty_sub_ctx_infs_det'. Qed.

Lemma sub_ctx_det : forall Δ A Σ Δ1 Δ2 A1 A2,
  sub_ctx Δ A Σ Δ1 A1 -> sub_ctx Δ A Σ Δ2 A2 -> Δ1 = Δ2 /\ A1 = A2.
Proof. hauto lq: on rew: off use: ty_sub_ctx_infs_det'. Qed.

Lemma infs_det : forall Γ Σ A1 A2,
  infs Γ Σ A1 -> infs Γ Σ A2 -> A1 = A2.
Proof. qauto l: on use: ty_sub_ctx_infs_det'. Qed.

Lemma eq_dec_env : forall (Γ : Env) Γ',
  {Γ = Γ'} + {Γ <> Γ'}.
Proof. repeat decide equality. Qed.

Lemma dec_close : forall Δ A,
  {close Δ A} + {~ close Δ A}.
Proof.
  intros Δ A. generalize dependent Δ.
  induction A; intro Δ; try sfirstorder.
  - destruct (dec_lookupTy Δ n). sauto lq: on.
    destruct (dec_lookupExTy Δ n). sauto lq: on use: lookupExTy_lookupExTy'.
    sauto lq: on use: lookupExTy'_lookupExTy, lookupTy_ExTy.
  - specialize (IHA1 Δ). specialize (IHA2 Δ). sauto q: on.
  - specialize (IHA (TyCons Δ)). sauto lq: on.
Qed.

Lemma dec_open : forall Δ A,
  {open Δ A} + {~ open Δ A}.
Proof.
  intros Δ A. generalize dependent Δ.
  induction A; intro Δ.
  - sauto lq: on. 
  - destruct (dec_lookupEx Δ n); sauto lq: on.
  - specialize (IHA1 Δ). specialize (IHA2 Δ). sauto q: on.
  - specialize (IHA (TyCons Δ)). sauto q: on.
Qed.

Lemma dec_grd_typ : forall Δ A,
  {A' | grd_typ Δ A A'} + {~ exists A', grd_typ Δ A A'}.
Proof.
  intros Δ A. generalize dependent Δ.
  induction A; intro Δ.
  - hauto l: on.
  - destruct (dec_lookupTy Δ n). sauto lq: on.
    destruct (dec_lookupExTy Δ n); sauto lq: on.
  - specialize (IHA1 Δ). specialize (IHA2 Δ). sauto q: on.
  - specialize (IHA (TyCons Δ)). sauto q: on.
Qed.

Fixpoint num_solved (Γ : Env) (A : Typ) : nat :=
  match A with
  | Int      => 0
  | TVar x   => if dec_lookupExTy' Γ x then 1 else 0
  | Arr A B  => num_solved Γ A + num_solved Γ B
  | All A    => num_solved (TyCons Γ) A
  end.

Lemma num_solved_RegularTyp : forall Γ A,
  RegularTyp Γ A -> num_solved Γ A = 0.
Proof.
  intros Γ A Hreg. dependent induction Hreg; simpl; try sfirstorder.
  hauto lq: on use: lookupExTy'_lookupExTy, lookupTy_ExTy, dec_lookupExTy'.
Qed.

Lemma num_solved_alt_env : forall A Γ Γ',
  (forall x, lookupExTy' Γ x <-> lookupExTy' Γ' x) ->
  num_solved Γ A = num_solved Γ' A.
Proof.
  intro A. induction A; simpl; intros Γ Γ' Hlk; sauto lq: on rew: off.
Qed.

Lemma num_solved_Ty_Ex : forall Δ A,
  num_solved (TyCons Δ) A = num_solved (ExCons Δ) A.
Proof. sauto lq: on rew: off use: num_solved_alt_env. Qed.

(* Lemma eq_dec_ctx : forall (Σ : Context) Σ',
  {Σ = Σ'} + {Σ <> Σ'}.
Proof. repeat decide equality. Qed. *)

Fixpoint num_all (A : Typ) : nat :=
  match A with
  | Arr A1 A2 => num_all A1 + num_all A2
  | All A' => 1 + num_all A'
  | _ => 0
  end.

Lemma dec_is_TLam : forall e,
  {e' | e = TLam e'} + {~ exists e', e = TLam e'}.
Proof. sauto lq: on rew: off. Qed.

Lemma dec_isCtxTyp : forall t,
  {t' | t = CtxTyp t'} + {~ exists t', t = CtxTyp t'}.
Proof. sauto lq: on rew: off. Qed.

Lemma dec_ty_sub_ctx_infs' : forall n,
  (forall Γ Σ e, tm_size e + ctx_size Σ < n ->
    {A | ty Γ Σ e A} + {~ exists A, ty Γ Σ e A}) *
  (forall k m Δ A Σ, ctx_size Σ < n -> num_solved Δ A < k -> num_all A < m ->
    {Δ' : Env & {A' : Typ & sub_ctx Δ A Σ Δ' A'}} + {~ exists Δ' A', sub_ctx Δ A Σ Δ' A'}) *
  (forall Γ Σ, ctx_size Σ < n ->
    {A | infs Γ Σ A} + {~ exists A, infs Γ Σ A}).
Proof.
  intro n. induction n. repeat split; try lia.
  destruct IHn as [[IHty IHsub] IHinfs]. repeat split.
  - intros Γ Σ e Hlt.
    assert (Tabs: forall e' t, e = TLam e' -> Σ = CtxTyp t -> {A | ty Γ Σ e A} + {~ exists A, ty Γ Σ e A}).
    { intros e' t Heq HΣ. subst.
      destruct t. 1 - 3 : sauto q: on.
      assert (Hlt': tm_size e' + ctx_size (CtxTyp t) < n) by (simpl in *; lia).
      eapply IHty with (Γ := TyCons Γ) in Hlt' as Hty.
      assert (Hlt''': tm_size e' + ctx_size CtxEmpty < n) by (simpl in *; lia).
      eapply IHty with (Γ := TyCons Γ) in Hlt''' as Hty'.
      destruct Hty as [[A Hty] | Hnty]. sauto lq: on.
      destruct Hty' as [[A Hty'] | Hnty'].
      + assert (Hlt'': ctx_size (CtxTyp (All t)) < n) by (simpl in *; lia).
        eapply IHsub with (Δ := SepCons Γ) (A := All A) in Hlt'' as Hsub; eauto.
        destruct Hsub as [[Γ' [B Hsub]] | Hnsub].
        * destruct (eq_dec_env Γ' (SepCons Γ)); subst. sauto lq: on rew: off.
          right. intros [B' Hc]. dependent destruction Hc; try sfirstorder use: NonEmpty_false.
          dependent destruction Hc; try sfirstorder use: NonEmpty_false.
          eapply ty_det in Hty'; eauto. subst.
          eapply sub_ctx_det in Hsub; eauto. sfirstorder.
        * right. intros [Γ' Hc]. dependent destruction Hc; try sfirstorder use: NonEmpty_false.
          dependent destruction Hc; try sfirstorder use: NonEmpty_false.
          eapply ty_det in Hty'; eauto. subst. sfirstorder.
      + right. intros [Γ' Hc]. dependent destruction Hc; try sfirstorder use: NonEmpty_false.
        dependent destruction Hc; try sfirstorder use: NonEmpty_false. }
    assert (Sub: GenericConsumer e -> NonEmpty Σ -> {A | ty Γ Σ e A} + {~ exists A, ty Γ Σ e A}).
    { intros Hgc Hne.
      eapply NonEmpty_ctx_size_gt0 in Hne as Hgt.
      assert (Hgt': tm_size e > 0) by apply tm_size_gt0.
      assert (Hlt': tm_size e + ctx_size CtxEmpty < n). { simpl. lia. }
      eapply IHty with (Γ := Γ) in Hlt' as Hempty.
      assert (Hlt'': ctx_size Σ < n) by lia.
      destruct Hempty as [[A Hty] | Hnty].
      - eapply IHsub with (Δ := SepCons Γ) (A := A) in Hlt'' as Hsub; eauto.
        destruct Hsub as [[Γ' [A' Hsub']] | Hneg].
        + destruct (eq_dec_env (SepCons Γ) Γ'); subst. sauto lq: on.
          destruct (dec_is_TLam e) as [[e' Heq] | Hntlam]; subst.
          * destruct (dec_isCtxTyp Σ) as [[t' Heq] | Hntctx]; subst. hauto l: on use: Tabs.
            right. intros [A'' Hc]. dependent destruction Hc; try sfirstorder use: NonEmpty_false.
            eapply ty_det in Hty; eauto. subst. eapply sub_ctx_det in Hsub'; eauto. sfirstorder.
          * right. intros [A'' Hc]. dependent destruction Hc; try sfirstorder use: NonEmpty_false.
            eapply ty_det in Hty; eauto. subst. eapply sub_ctx_det in Hsub'; eauto. sfirstorder.
        + destruct (dec_is_TLam e) as [[e' Heq] | Hntlam]; subst.
          * destruct (dec_isCtxTyp Σ) as [[t' Heq] | Hntctx]; subst. hauto l: on use: Tabs.
            right. intros [A'' Hc]. dependent destruction Hc; try sfirstorder use: NonEmpty_false.
            eapply ty_det in Hty; eauto. subst. sfirstorder.
          * right. intros [A'' Hc]. dependent destruction Hc; try sfirstorder use: NonEmpty_false.
            eapply ty_det in Hty; eauto. subst. sfirstorder.
      - destruct (dec_is_TLam e) as [[e' Heq] | Hntlam]; subst.
        + destruct (dec_isCtxTyp Σ) as [[t' Heq] | Hntctx]; subst. hauto l: on use: Tabs.
          right. intros [Γ'' Hc]. dependent destruction Hc; try sfirstorder use: NonEmpty_false.
        + right. intros [Γ'' Hc]. dependent destruction Hc; try sfirstorder use: NonEmpty_false. }
    destruct e; simpl in *.
    + destruct (dec_CtxEmpty Σ); subst; try sfirstorder.
      destruct (dec_TRegular Γ); sauto q: on.
    + destruct (dec_CtxEmpty Σ); subst; try sfirstorder.
      destruct (dec_lookupTm Γ n0) as [[A' Hlk] | Hnlk].
      * destruct (dec_TRegular Γ). sauto lq: on.
        right. intros [Γ' Hc]. dependent destruction Hc; sfirstorder use: NonEmpty_false.
      * right. intros [Γ' Hc]. dependent destruction Hc; try sfirstorder use: NonEmpty_false.
    + destruct Σ.
      * sauto lq: on.
      * destruct t. 1, 2, 4 : sauto lq: on.
        assert (Hlt': tm_size e + ctx_size (CtxTyp t2) < n). { simpl in *. lia. }
        eapply IHty with (Γ := TmCons Γ t1) in Hlt' as Hty.
        destruct Hty as [[A Hty] | Hnty]. sauto lq: on.
        right. intros [Γ' Hc]. dependent destruction Hc; try sfirstorder use: NonEmpty_false.
      * assert (Hlt': tm_size t + ctx_size CtxEmpty < n). { simpl in *. lia. }
        assert (Hlt'': tm_size e + ctx_size (tm_shift_ctx Σ 0) < n).
        { rewrite ctx_size_tm_shift. simpl in *. lia. }
        eapply IHty with (Γ := Γ) in Hlt' as Hty.
        destruct Hty as [[A Hty] | Hnty].
        -- eapply IHty with (Γ := TmCons Γ A) in Hlt'' as Hty'.
           destruct Hty' as [[A' Hty'] | Hnty']. sauto lq: on.
           right. intros [Γ' Hc]. dependent destruction Hc; try sfirstorder use: NonEmpty_false.
           eapply ty_det in Hty; eauto. sfirstorder.
        -- right. intros [Γ' Hc]. dependent destruction Hc; try sfirstorder use: NonEmpty_false.
      * sauto lq: on.
    + assert (Hlt': tm_size e1 + ctx_size (CtxTrm e2 Σ) < n). { simpl in *. lia. }
      eapply IHty with (Γ := Γ) in Hlt' as Hty.
      destruct Hty as [[A Hty] | Hnty].
      * destruct A; try solve [right; intros [Γ' Hc]; dependent destruction Hc; try sfirstorder;
          eapply ty_det in Hty; eauto; sfirstorder].
        sauto lq: on.
      * right. intros [Γ' Hc]. dependent destruction Hc; try sfirstorder use: NonEmpty_false. 
    + destruct (dec_CtxEmpty Σ); subst; try sfirstorder.
      assert (Hlt': tm_size e + ctx_size (CtxTyp t) < n). { simpl in *. lia. }
      eapply IHty with (Γ := Γ) in Hlt' as Hty.
      destruct Hty as [[A Hty] | Hnty]. sauto lq: on.
      right. intros [Γ' Hc]. dependent destruction Hc; try sfirstorder use: NonEmpty_false.
    + destruct (dec_CtxEmpty Σ); subst; try sfirstorder.
      assert (Hlt': tm_size e + ctx_size CtxEmpty < n) by lia.
      eapply IHty with (Γ := TyCons Γ) in Hlt' as Hty.
      destruct Hty as [[A Hty] | Hnty]. sauto lq: on.
      right. intros [Γ' Hc]. dependent destruction Hc; try sfirstorder use: NonEmpty_false.
    + assert (Hlt': tm_size e + ctx_size (CtxTApp t Σ) < n). { simpl in *. lia. }
      eapply IHty with (Γ := Γ) in Hlt' as Hty.
      destruct Hty as [[A Hty] | Hnty].
      * destruct A; try solve [right; intros [Γ' Hc]; dependent destruction Hc; try sfirstorder;
          eapply ty_det in Hty; eauto; sfirstorder].
        sauto lq: on.
      * right. intros [Γ' Hc]. dependent destruction Hc; try sfirstorder use: NonEmpty_false.
  - intro k. induction k; try lia.
    intro m. induction m; try lia.
    intros Δ A Σ Hlt1 Hlt2 Hlt3. destruct Σ.
    + destruct (dec_SRegular Δ). 2 : sauto lq: on rew: off.
      destruct (dec_close Δ A) as [Hc | Hnc]. 2 : sauto lq: on.
      destruct (dec_grd_typ Δ A) as [[A' Hgrd] | Hngrd]; sauto lq: on.
    + destruct (dec_sub Δ A Pos t) as [[Δ' Hsub] | Hnsub]; sauto lq: on.
    + destruct A. sauto lq: on rew: off.
      * destruct (dec_SRegular Δ). 2 : sauto lq: on use: sub_ctx_SRegular_in.
        destruct (dec_lookupExTy Δ n0) as [[A Hlk] | Hnlk].
        -- eapply SRegular_lookupExTy_RegularTyp in Hlk as Hreg; eauto.
           eapply num_solved_RegularTyp in Hreg. simpl in *.
           eapply lookupExTy_lookupExTy' in Hlk as Hlk'.
           assert (Hlt2': num_solved Δ A < k) by hauto l: on.
           eapply IHk with (Σ := CtxTrm t Σ) in Hlt2' as Hsub; eauto; eauto.
           destruct Hsub as [[Δ' [A' Hsub]] | Hnsub].
           ++ destruct (eq_dec_env Δ' Δ); subst.
              ** destruct A'; sauto qb: on drew: off.
              ** right. intros [Δ'' [A'' Hcontra]].
                 dependent destruction Hcontra; try sfirstorder.
                 --- eapply lookupExTy_det in Hlk; eauto. subst.
                     eapply sub_ctx_det in Hcontra; try sfirstorder.
                 --- sauto lq: on rew: off use: substEnv_Ex, lookupEx_ExTy.
           ++ right. intros [Δ' [A' Hcontra]].
              dependent destruction Hcontra; try sfirstorder.
              ** eapply lookupExTy_det in Hlk; eauto. sfirstorder.
              ** hauto lq: on rew: off use: substEnv_Ex, lookupEx_ExTy.
        -- assert (Hlt': ctx_size Σ < n). { simpl in *. lia. }
           eapply IHinfs with (Γ := Δ) (Σ := Σ) in Hlt' as Hinf.
           assert (Hlt'': tm_size t + ctx_size CtxEmpty < n). { simpl in *. lia. }
           eapply IHty with (Γ := Δ) (Σ := CtxEmpty) (e := t) in Hlt'' as Hty; eauto.
           destruct Hinf as [[B Hinf] | Hninf]. 2 : sauto lq: on drew: off.
           destruct Hty as [[A Hty] | Hnty]. 2 : sauto lq: on drew: off.
           destruct (dec_substEnv (Arr A B) n0 Δ) as [[Ψ Hsubst] | Hnsubst].
           ** sauto lq: on.
           ** right. intros [Δ' [A' Hcontra]].
              dependent destruction Hcontra; try sfirstorder.
              dependent destruction H.
              eapply infs_det in Hinf; eauto. subst.
              eapply ty_det in Hty; eauto. subst. sfirstorder.
      * assert (Hlt': ctx_size Σ < n). { simpl in *. lia. }
        eapply IHsub with (Δ := Δ) (A := A2) in Hlt' as Hsub; eauto.
        destruct Hsub as [[Ω [A2' Hsub]] | Hnsub]. 2 : sauto lq: on drew: off.
        destruct (dec_close Ω A1) as [Hc | Hnc].
        -- destruct (dec_open Ω A1) as [Ho | Hno].
           sfirstorder use: open_close_false.
           destruct (dec_grd_typ Ω A1) as [[A1' Hgrd] | Hngrd].
           ++ assert (Hlt'': tm_size t + ctx_size (CtxTyp A1') < n). { simpl in *. lia. }
              eapply IHty with (Γ := rm_sep Ω) in Hlt'' as Hty.
              destruct Hty as [[A'' Hty] | Hnty]. sauto q: on dep: on.
              right. intros [Ω' [A' Hcontra]]. dependent destruction Hcontra; try sfirstorder.
              ** eapply sub_ctx_det in Hsub; eauto. destruct Hsub as [Heq1 Heq2]. subst. 
                 eapply grd_typ_det in Hgrd; eauto. subst. sfirstorder.
              ** eapply sub_ctx_det in Hsub; eauto. destruct Hsub as [Heq1 Heq2]. subst. scongruence.
           ++ right. intros [Ω' [A' Hcontra]]. dependent destruction Hcontra; try sfirstorder;
              eapply sub_ctx_det in Hsub; eauto; destruct Hsub as [Heq1 Heq2]; sfirstorder.
        -- destruct (dec_open Ω A1) as [Ho | Hno].
           ++ assert (Hlt'': tm_size t + ctx_size CtxEmpty < n). { simpl in *. lia. }
              eapply IHty with (Γ := rm_sep Ω) in Hlt'' as Hty.
              destruct Hty as [[C Hty] | Hnty].
              ** destruct (dec_sub Ω C Neg A1) as [[Ψ Hsub'] | Hnsub']. sauto l: on.
                 right. intros [Ω' [A' Hcontra]].
                 dependent destruction Hcontra; try sfirstorder.
                 --- eapply sub_ctx_det in Hsub; eauto. sfirstorder.
                 --- eapply sub_ctx_det in Hsub; eauto. destruct Hsub as [Heq1 Heq2]. subst.
                     eapply ty_det in Hty; eauto. sfirstorder.
              ** right. intros [Ω' [A' Hcontra]].
                 dependent destruction Hcontra; try sfirstorder;
                   eapply sub_ctx_det in Hsub; eauto; destruct Hsub as [Heq1 Heq2]; sfirstorder.
           ++ right. intros [Ω' [A' Hcontra]].
              dependent destruction Hcontra; try sfirstorder;
                eapply sub_ctx_det in Hsub; eauto; sfirstorder.
      * assert (Hlt': ctx_size (CtxTrm (ty_shift_tm t 0) (ty_shift_ctx Σ 0)) < S n).
        { simpl in *. rewrite tm_size_ty_shift_tm. rewrite ctx_size_ty_shift. lia. }
        assert (Hlt'': num_all A < m). { simpl in *. lia. }
        assert (Hlt''': num_solved (Δ, ^) A < S k).
        { simpl in *. scongruence use: num_solved_Ty_Ex. }
        eapply IHm with (Δ := ExCons Δ) in Hlt'' as Hsub; eauto; simpl in *.
        destruct Hsub as [[Δ' [A' Hsub]] | Hnsub].
        -- destruct Δ'; try solve [right; intros [Δ'' [A'' Hcontra]];
             dependent destruction Hcontra; eapply sub_ctx_det in Hsub; eauto; hauto q: on].
           ++ destruct A'. 1, 2, 4 : sauto q: on.
              destruct (dec_ty_unshift A'1 0) as [[A1' Heq1] | Hneq1]; subst.
              ** destruct (dec_ty_unshift A'2 0) as [[A2' Heq2] | Hneq2]; subst. sauto lq: on.
                 right. intros [Δ'' [A'' Hcontra]]. dependent destruction Hcontra; try sfirstorder;
                 eapply sub_ctx_det in Hsub; eauto; sfirstorder.
              ** right. intros [Δ'' [A'' Hcontra]]. dependent destruction Hcontra; try sfirstorder;
                 eapply sub_ctx_det in Hsub; eauto; sfirstorder.
           ++ destruct A'. 1, 2, 4 : sauto q: on.
              destruct (dec_ty_unshift A'1 0) as [[A1' Heq1] | Hneq1]; subst.
              ** destruct (dec_ty_unshift A'2 0) as [[A2' Heq2] | Hneq2]; subst. sauto lq: on.
                 right. intros [Δ'' [A'' Hcontra]]. dependent destruction Hcontra; try sfirstorder;
                 eapply sub_ctx_det in Hsub; eauto; sfirstorder.
              ** right. intros [Δ'' [A'' Hcontra]]. dependent destruction Hcontra; try sfirstorder;
                 eapply sub_ctx_det in Hsub; eauto; sfirstorder.
        -- sauto lq: on.
    + destruct A.
      * sauto lq: on.
      * destruct (dec_SRegular Δ). 2 : sauto lq: on rew: off use: sub_ctx_SRegular_in.
        destruct (dec_lookupExTy Δ n0) as [[A Hlk] | Hnlk]. 2 : sauto lq: on rew: off.
        assert (0 < k) by hauto l: on use: lookupExTy_lookupExTy'.
        eapply SRegular_lookupExTy_RegularTyp in Hlk as Hreg; eauto.
        eapply num_solved_RegularTyp in Hreg.
        assert (Hlt2': num_solved Δ A < k) by scongruence.
        eapply IHk with (Σ := CtxTApp t Σ) in Hlt2' as Hsub; eauto.
        destruct Hsub as [[Δ' [A' Hsub]] | Hnsub].
        -- destruct (eq_dec_env Δ' Δ); subst.
           ++ destruct A'; sauto q: on.
           ++ right. intros [Δ'' [A'' Hcontra]].
              dependent destruction Hcontra; try sfirstorder.
              eapply lookupExTy_det in Hlk; eauto. subst.
              eapply sub_ctx_det in Hsub; eauto. sfirstorder.
        -- right. intros [Δ'' [A'' Hcontra]].
           dependent destruction Hcontra; try sfirstorder.
           eapply lookupExTy_det in Hlk; eauto. sfirstorder. 
      * sauto lq: on.
      * assert (Hlt': ctx_size (ty_shift_ctx Σ 0) < n).
        { simpl in *. rewrite ctx_size_ty_shift. lia. }
        eapply IHsub with (Δ := ExTyCons Δ t) (A := A) in Hlt' as Hsub; eauto.
        destruct Hsub as [[Δ' [A' Hsub]] | Hnsub].
        -- destruct Δ'; try solve [right; intros [Δ'' [A'' Hcontra]];
            dependent destruction Hcontra; eapply sub_ctx_det in Hsub; eauto; hauto q: on].
            destruct (eq_dec_ty t t0); subst. sauto lq: on.
            right. intros [Δ'' [A'' Hcontra]]. dependent destruction Hcontra; try sfirstorder.
            eapply sub_ctx_det in Hsub; eauto. sfirstorder.
        -- right. intros [Δ'' [A'' Hcontra]]. dependent destruction Hcontra; try sfirstorder. 
  - intros Γ Σ Hlt.
    destruct Σ. 1, 4 : sauto lq: on rew: off.
    + destruct (dec_TRegular Γ). 2 : sauto q: on rew: off.
      destruct (dec_RegularTyp Γ t) as [Hreg' | Hnreg]. 2 : sauto lq: on.
      sauto lq: on.
    + assert (Hlt': tm_size t + ctx_size CtxEmpty < n). { simpl in *. lia. }
      eapply IHty with (Γ := Γ) in Hlt' as Hty.
      destruct Hty as [[A Hty] | Hnty]. 2 : sauto lq: on rew: off.
      assert (Hlt'' : ctx_size Σ < n). { simpl in *. lia. }
      eapply IHinfs with (Γ := Γ) (Σ := Σ) in Hlt'' as Hinf; eauto.
      destruct Hinf as [[A' Hinf] | Hninf]; sauto lq: on rew: off.
Qed.

Theorem dec_ty : forall Γ Σ e,
  {A | ty Γ Σ e A} + {~ exists A, ty Γ Σ e A}.
Proof. hauto lq: on use: dec_ty_sub_ctx_infs'. Qed.

Theorem dec_sub_ctx : forall Δ A Σ,
  {Δ' : Env & {A' : Typ & sub_ctx Δ A Σ Δ' A'}} + {~ exists Δ' A', sub_ctx Δ A Σ Δ' A'}.
Proof. hauto lq: on use: dec_ty_sub_ctx_infs'. Qed.

Theorem dec_infs : forall Γ Σ,
  {A | infs Γ Σ A} + {~ exists A, infs Γ Σ A}.
Proof. hauto lq: on use: dec_ty_sub_ctx_infs'. Qed.

Recursive Extraction dec_ty.