Require Import Syntax.
Require Import Algo.
Require Import Lia.
From Hammer Require Import Tactics.
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

Fixpoint tm_size (e : Trm) : nat :=
  match e with
  | Lit _ => 1
  | Var _ => 1
  | Lam e' => 1 + tm_size e'
  | App e1 e2 => 3 + tm_size e1 + tm_size e2
  | Ann e' _ => 1 + tm_size e'
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

Lemma ty_sub_ctx_det' : forall n,
  (forall Γ Σ e A A', tm_size e + ctx_size Σ < n ->
    ty Γ Σ e A -> ty Γ Σ e A' -> A = A') /\
  (forall m Δ A Σ Δ1 Δ2 A1 A2, ctx_size Σ < n -> ty_size A + ctx_size Σ < m ->
    sub_ctx Δ A Σ Δ1 A1 -> sub_ctx Δ A Σ Δ2 A2 -> Δ1 = Δ2 /\ A1 = A2).
Proof.
  intro n. induction n. split; try lia.
  destruct IHn as [IHty IHsub]. split.
  - intros Γ Σ e A A' Hlt Hty1 Hty2.
    dependent destruction Hty1; dependent destruction Hty2; simpl in *;
      try sfirstorder use: NonEmpty_false, lookupTm_det;
      try solve [eapply IHty in Hty1; eauto; simpl; try lia; sfirstorder].
    + eapply IHty in Hty1_1; eauto; simpl; try lia. subst.
      eapply IHty in Hty1_2; eauto. sfirstorder.
      rewrite ctx_size_tm_shift. lia.
    + assert (Hlt': tm_size g < n). { eapply NonEmpty_ctx_size_gt0 in H. lia. }
      assert (Hlt'': ctx_size Σ < n). { specialize (tm_size_gt0 g). lia. }
      eapply IHty in Hty1; eauto; simpl; try lia. subst.
      eapply IHsub with (Δ1 := (Γ ⋈)) in H1; eauto; simpl; try lia. sfirstorder.
  - intro m. induction m; try lia.
    intros Δ A Σ Δ1 Δ2 A1 A2 Hlt1 Hlt2 Hsub1 Hsub2.
    dependent destruction Hsub1; dependent destruction Hsub2; simpl in *;
      try sfirstorder use: grd_typ_det, sub_det, open_close_false.
    + eapply grd_typ_det in H0; eauto. subst.
      eapply IHty in H1; eauto; simpl; try lia. subst.
      eapply IHsub in Hsub1; eauto; simpl; try lia. sfirstorder.
    + eapply IHty in H0; eauto; simpl; try lia. subst.
      eapply sub_det in H1; eauto; simpl; try lia. subst.
      eapply IHsub in Hsub1; eauto; simpl; try lia. sfirstorder.
    + eapply IHm in Hsub1; eauto; simpl;
        try rewrite tm_size_ty_shift_tm; try rewrite ctx_size_ty_shift; try lia.
      sfirstorder use: ty_unshift_det.
    + eapply IHsub in Hsub1; eauto; simpl; try rewrite ctx_size_ty_shift; try lia; try sfirstorder.
Qed.

Lemma ty_det : forall Γ Σ e A A', ty Γ Σ e A -> ty Γ Σ e A' -> A = A'.
Proof. sauto lq: on use: ty_sub_ctx_det'. Qed.

Lemma sub_ctx_det : forall Δ A Σ Δ1 Δ2 A1 A2,
  sub_ctx Δ A Σ Δ1 A1 -> sub_ctx Δ A Σ Δ2 A2 -> Δ1 = Δ2 /\ A1 = A2.
Proof. hauto lq: on rew: off use: ty_sub_ctx_det'. Qed.

Lemma dec_ty_sub_ctx' : forall n,
  (forall Γ Σ e, tm_size e + ctx_size Σ < n ->
    {A | ty Γ Σ e A} + {~ exists A, ty Γ Σ e A}) *
  (forall m Δ A Σ, ctx_size Σ < n -> ty_size A + ctx_size Σ < m ->
    {Δ' : Env & {A' : Typ & sub_ctx Δ A Σ Δ' A'}} + {~ exists Δ' A', sub_ctx Δ A Σ Δ' A'}).
Admitted.

Theorem dec_ty : forall Γ Σ e,
  {A | ty Γ Σ e A} + {~ exists A, ty Γ Σ e A}.
Proof. hauto lq: on use: dec_ty_sub_ctx'. Qed.

Theorem dec_sub_ctx : forall Δ A Σ,
  {Δ' : Env & {A' : Typ & sub_ctx Δ A Σ Δ' A'}} + {~ exists Δ' A', sub_ctx Δ A Σ Δ' A'}.
Proof. hauto lq: on use: dec_ty_sub_ctx'. Qed.
