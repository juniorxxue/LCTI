Require Import Syntax.

Inductive ty : env -> context -> term -> type -> Prop :=
| tyInt : forall {Gamma n}, ty Gamma ctxEmpty (Lit n) Int
| tyVar : forall {Gamma x A},
    lookup Gamma x A ->
    ty Gamma ctxEmpty (Var x) A
| tyAnn : forall {Gamma e A B},
    ty Gamma (ctxType A) e B ->
    ty Gamma ctxEmpty (Ann e A) A
| tyApp : forall {Gamma Sigma e1 e2 A B},
    ty Gamma (ctxTerm e2 Sigma) e1 (Arr A B) ->
    ty Gamma Sigma (App e1 e2) B
| tyLam1 : forall {Gamma A B C e},
    ty (TBCons Gamma A) (ctxType B) e C ->
    ty Gamma (ctxType (Arr A B)) (Lam e) (Arr A C)
| tyLam2 : forall {Gamma Sigma A B e e2},
    ty Gamma ctxEmpty e2 A ->
    ty (TBCons Gamma A) (ctxtmshift Sigma 0) e B ->
    ty Gamma (ctxTerm e2 Sigma) (Lam e) (Arr A B)
| tySub : forall {Gamma Sigma g A},
    ty Gamma ctxEmpty g A ->
    nonEmpty Sigma ->
    genericConsumer g ->
    sub Gamma A Sigma ->
    ty Gamma Sigma g A
| tyTAbs : forall {Gamma e A},
    ty (TyCons Gamma) ctxEmpty e A ->
    ty Gamma ctxEmpty (TLam e) (Fall A)
| tyTApp : forall {Gamma Sigma e A B},
    ty Gamma (ctxTApp A Sigma) e (Fall B) ->
    ty Gamma Sigma (TApp e A) (subst B 0 A)
with sub : env -> type -> context -> Prop :=
| subEmpty : forall {Gamma A},
    sub Gamma A ctxEmpty
| subRefl : forall {Gamma A},
    sub Gamma A (ctxType A)
| subArr : forall {Gamma Sigma e A B C},
    sub Gamma B Sigma ->
    ty Gamma (ctxType A) e C ->
    sub Gamma (Arr A B) (ctxTerm e Sigma)
| subTApp : forall {Gamma Sigma A B},
    sub Gamma (subst A 0 B) Sigma ->
    sub Gamma (Fall A) (ctxTApp B Sigma)
.

Notation "Gamma ⊢ Sigma ⇒ e ⇒ A" := (ty Gamma Sigma e A) (at level 200).
Notation "Gamma ⊢ A ≤ Sigma" := (sub Gamma A Sigma) (at level 200).
