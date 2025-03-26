Require Import Syntax.
Require Import Algo.
Require Import Lia.
From Hammer Require Import Tactics.
Require Import Coq.Program.Equality.

(*
for references of previous systems:
1. https://types.hk/proof/contextual/README.html
2. https://github.com/juniorxxue/contextual-typing/blob/main/paper_extended.pdf (Page 32)
*)

Fixpoint term_size (e : term) : nat :=
  match e with
  | Lit _ => 1
  | Var _ => 1
  | Lam e' => 1 + term_size e'
  | App e1 e2 => 2 + term_size e1 + term_size e2
  | Ann e' _ => 1 + term_size e'
  | TLam e' => 1 + term_size e'
  | TApp e' _ => 1 + term_size e'
  end.

Fixpoint context_size (Σ : context) : nat :=
  match Σ with
  | ctxEmpty => 0
  | ctxType _ => 0
  | ctxTerm e Σ' => 1 + term_size e + context_size Σ'
  | ctxTApp _ Σ' => 1 + context_size Σ'
  end.

Fixpoint type_size (A : type) : nat :=
  match A with
  | Int => 1
  | TVar _ => 1
  | Arr A1 A2 => 1 + type_size A1 + type_size A2
  | Fall A' => 1 + type_size A'
  end.

Lemma dec_NonEmpty Σ :
  {Σ = ctxEmpty} + {nonEmpty Σ}.
Proof. sauto lq: on. Qed.

Lemma dec_lookup Γ n :
  (exists A, lookup Γ n A) \/ ~ (exists A, lookup Γ n A).
Proof.
  revert n; induction Γ; intros n.
  - sauto lq: on.
  - destruct n.
    + sauto lq: on.
    + destruct (IHΓ n) as [[A H] | H]; sauto lq: on.
  - destruct (IHΓ n) as [[A H] | H]; sauto lq: on.
Qed.

Lemma lookup_det Γ n A A' :
  lookup Γ n A -> lookup Γ n A' -> A = A'.
Proof.
  revert n A A'; induction Γ; intros n A A' H1 H2; sauto lq: on rew: off.
Qed.

Lemma dec_ty_sub : forall n,
  (forall Γ Σ e, term_size e + context_size Σ < n ->
    (exists A, ty Γ Σ e A) \/ ~ (exists A, ty Γ Σ e A)) /\
  (forall Γ Σ A, context_size Σ < n ->
    sub Γ A Σ \/ ~ sub Γ A Σ).
Proof.
  intros n. induction n. split; try lia.
  destruct IHn as [IHty IHsub]. split.
  - intros Γ Σ e Hlt.
    destruct e; simpl in *.
    + destruct (dec_NonEmpty Σ).
      * sauto lq: on rew: off.
      * assert (DecSub: sub Γ Int Σ \/ ~ sub Γ Int Σ).
        { eapply IHsub. lia. }
        destruct DecSub.
        -- sauto lq: on.
        -- right. intros [A Contra].
           dependent destruction Contra.
           ++ hauto lq: on.
           ++ dependent destruction Contra.
              sfirstorder. sauto lq: on.
    + destruct (dec_NonEmpty Σ); destruct (dec_lookup Γ n0) as [[A Hlkup] | Hlkup].
      * sauto lq: on.
      * right. intros [A Contra].
        dependent destruction Contra; sauto lq: on.
      * assert (DecSub: sub Γ A Σ \/ ~ sub Γ A Σ).
        { eapply IHsub. lia. }
        destruct DecSub.
        -- sauto lq: on.
        -- right. intros [A' Contra].
          dependent destruction Contra.
          ++ sauto lq: on use: lookup_det.
          ++ dependent destruction Contra.
            ** eapply lookup_det with (A := A0) in Hlkup; eauto.
               sfirstorder.
            ** sauto lq: on.
      * right. intros [A Contra].
        dependent destruction Contra.
        -- sfirstorder use: lookup_det.
        -- dependent destruction Contra; sauto lq: on.
    + admit.
    + admit.
    + admit.
    + admit.
    + admit. 
  - intros Γ Σ A Hlt.
    destruct Σ; simpl in *.
    + sfirstorder.
    + admit.
    + destruct A.
      * sauto lq: on.
      * sauto lq: on.
      * assert (DecSub: sub Γ A2 Σ \/ ~ sub Γ A2 Σ).
        { eapply IHsub. lia. }
        assert (DecTy: (exists C, ty Γ (ctxType A1) t C) \/
                     ~ (exists C, ty Γ (ctxType A1) t C)).
        { eapply IHty. simpl. lia. }
        destruct DecSub; destruct DecTy as [[C Hty] | Hty]; sauto lq: on.
      * sauto lq: on.
    + right. intros Contra.
      dependent destruction Contra.
Admitted.
