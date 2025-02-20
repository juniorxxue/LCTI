Require Import Coq.Init.Nat.
Require Import Coq.Arith.Compare_dec.

(**
syntax in this rule align with Agda code
https://github.com/juniorxxue/contextual-polymorphic/blob/main/agda/Explicit/Common.agda
**)

(* I may misuse Set and Prop *)

(** * Types *)

Inductive type : Set :=
| Int : type
| TVar : nat -> type
| Arr : type -> type -> type
| Fall : type -> type.

(* notations are only used for displaying *)
Notation "‶ X" := (TVar X) (at level 13, right associativity).
Notation "A `→ B" := (Arr A B) (at level 11, right associativity).
Notation "`∀ A" := (Fall A) (at level 12, right associativity).

(** * Terms *)

Inductive term : Set :=
| Lit   : nat -> term
| Var   : nat -> term
| Lam   : term -> term
| App   : term -> term -> term
| Ann   : term -> type -> term
| TLam  : term -> term
| TApp  : term -> type -> term.


Notation "ƛ~ e"      := (Lam e) (at level 51, right associativity).
Notation "e1 · e2"  := (App e1 e2) (at level 40, left associativity).
Notation "e ⦂ A"    := (Ann e A) (at level 50, left associativity).
Notation "Λ~ e"  := (TLam e) (at level 52, right associativity).
Notation "e @ A "  := (TApp e A) (at level 50, left associativity).

Inductive context : Set :=
| ctxEmpty : context
| ctxType  : type -> context
| ctxTerm  : term -> context -> context
| ctxTApp  : type -> context -> context.

Notation "□" := ctxEmpty (at level 50).
Notation "τ~ A" := (ctxType A) (at level 50).
Notation "[ e ]↝ Sigma" := (ctxTerm e Sigma) (at level 53, right associativity).
Notation "⟦ A ⟧↝ Sigma" := (ctxTApp A Sigma) (at level 54, right associativity).

Inductive nonEmpty : context -> Set :=
| neType : forall {A}, nonEmpty (ctxType A)
| neTerm : forall {e Sigma}, nonEmpty (ctxTerm e Sigma)
| neTApp : forall {A Sigma}, nonEmpty (ctxTApp A Sigma)
.

Inductive genericConsumer : term -> Set :=
| gcLit : forall {n}, genericConsumer (Lit n)
| gcVar : forall {x}, genericConsumer (Var x)
| gcAnn : forall {e A}, genericConsumer (Ann e A)
| gcTLam : forall {e}, genericConsumer (TLam e)
.

Inductive env : Set :=
| Empty : env
| TBCons : env -> type -> env (* term binding*)
| TyCons : env -> env. (* type variables *)

Notation "∅" := Empty (at level 60).
Notation "Gamma , A" := (TBCons Gamma A) (at level 60, right associativity).
Notation "Gamma , ⋅" := (TyCons Gamma) (at level 61, right associativity).

(* The function f(i,j) = if i<=j then j+1 else j *)
Definition punchIn (k : nat) (X : nat) : nat :=
  if k <=? X then X + 1 else X.

(*
(* A ↑ty k ⇘ A' *)
Inductive tyshift : type -> nat -> type -> Set :=
| sfInt : forall {k}, tyshift Int k Int
| sfVar : forall {X k}, tyshift (TVar X) k (TVar (punchIn k X))
| sfArr : forall {A A' B B' k}, tyshift A k A' -> tyshift B k B' -> tyshift (Arr A B) k (Arr A' B')
| sfFall : forall {A A' k}, tyshift A (S k) A' -> tyshift (Fall A) k (Fall A')
.

Notation "A ↑ty k ⇘ A'" := (tyshift A k A') (at level 100).
*)

Fixpoint tyshift (A : type) (k : nat) : type :=
  match A with
  | Int => Int
  | TVar X => TVar (punchIn k X)
  | Arr A B => Arr (tyshift A k) (tyshift B k)
  | Fall A => Fall (tyshift A (S k))
  end.

Fixpoint tmshift (e : term) (k : nat) : term :=
  match e with
  | Lit n => Lit n
  | Var x => Var (punchIn k x)
  | Lam e => Lam (tmshift e (S k))
  | App e1 e2 => App (tmshift e1 k) (tmshift e2 k)
  | Ann e A => Ann (tmshift e k) A
  | TLam e => TLam (tmshift e k)
  | TApp e A => TApp (tmshift e k) A
  end.

Fixpoint ctxtmshift (Sigma : context) (k : nat) : context :=
  match Sigma with
  | ctxEmpty => ctxEmpty
  | ctxType A => ctxType A
  | ctxTerm e Sigma => ctxTerm (tmshift e k) (ctxtmshift Sigma k)
  | ctxTApp A Sigma => ctxTApp A (ctxtmshift Sigma k)
  end.

(* (x : A) in Gamma*)
Inductive lookup : env -> nat -> type -> Set :=
| lkZ : forall {Gamma A}, lookup (TBCons Gamma A) 0 A
| lkSTB : forall {Gamma A B x}, lookup Gamma x A -> lookup (TBCons Gamma B) (S x) A
| lkSTy : forall {Gamma A x},
    lookup Gamma x A -> lookup (TyCons Gamma) x (tyshift A 0).

(* A [k / T] *)
Fixpoint subst (A : type) (k : nat) (T : type) : type :=
  match A with
  | Int => Int
  | TVar X => match lt_eq_lt_dec X k with
             | inleft (left _) => TVar X
             | inleft (right _) => T
             | inright _ => TVar (X - 1)
             end
  | Arr A B => Arr (subst A k T) (subst B k T)
  | Fall A => Fall (subst A (S k) (tyshift T 0))
  end.
