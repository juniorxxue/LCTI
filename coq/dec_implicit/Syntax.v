Require Import Coq.Init.Nat.
Require Import Coq.Arith.Compare_dec.

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

Inductive nonEmpty : context -> Prop :=
| neType : forall {A}, nonEmpty (ctxType A)
| neTerm : forall {e Sigma}, nonEmpty (ctxTerm e Sigma)
| neTApp : forall {A Sigma}, nonEmpty (ctxTApp A Sigma)
.

Inductive genericConsumer : term -> Prop :=
| gcLit : forall {n}, genericConsumer (Lit n)
| gcVar : forall {x}, genericConsumer (Var x)
| gcAnn : forall {e A}, genericConsumer (Ann e A)
| gcTLam : forall {e}, genericConsumer (TLam e)
.

Inductive env : Set :=
| Empty : env
| TBCons : env -> type -> env (* term binding*)
| ExCons : env -> env (* existential variables *)
| TyCons : env -> env (* type variables *)
| ExTypCons : env -> type -> env (* existential variables with type *)
| SepCons : env -> env
.

Notation "∅" := Empty (at level 60).
Notation "Gamma , A" := (TBCons Gamma A) (at level 60, right associativity).
Notation "Gamma , ^" := (ExCons Gamma) (at level 61, right associativity).
Notation "Gamma , ⋅" := (TyCons Gamma) (at level 61, right associativity).
Notation "Gamma , = A" := (ExTypCons Gamma A) (at level 61, right associativity).
Notation "Gamma ⋈" := (SepCons Gamma) (at level 60, right associativity).

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

Fixpoint tmtyshift (e : term) (k : nat) : term :=
  match e with
  | Lit n => Lit n
  | Var x => Var x
  | Lam e => Lam (tmtyshift e k)
  | App e1 e2 => App (tmtyshift e1 k) (tmtyshift e2 k)
  | Ann e A => Ann (tmtyshift e k) (tyshift A k)
  | TLam e => TLam (tmtyshift e (S k))
  | TApp e A => TApp (tmtyshift e k) (tyshift A k)
  end.

Fixpoint ctxtyshift (Sigma : context) (k : nat) : context :=
  match Sigma with
  | ctxEmpty => ctxEmpty
  | ctxType A => ctxType (tyshift A k)
  | ctxTerm e Sigma => ctxTerm (tmtyshift e k) (ctxtyshift Sigma k)
  | ctxTApp A Sigma => ctxTApp (tyshift A k) (ctxtyshift Sigma k)
  end.

Fixpoint ctxtmshift (Sigma : context) (k : nat) : context :=
  match Sigma with
  | ctxEmpty => ctxEmpty
  | ctxType A => ctxType A
  | ctxTerm e Sigma => ctxTerm (tmshift e k) (ctxtmshift Sigma k)
  | ctxTApp A Sigma => ctxTApp A (ctxtmshift Sigma k)
  end.

(* (x : A) in Gamma*)
Inductive lookup : env -> nat -> type -> Prop :=
| lkZ : forall {Gamma A}, lookup (TBCons Gamma A) 0 A
| lkSTB : forall {Gamma A B x}, lookup Gamma x A -> lookup (TBCons Gamma B) (S x) A
| lkSTEx : forall {Gamma x A}, lookup Gamma x A -> lookup (ExCons Gamma) x (tyshift A 0)
| lkSTy : forall {Gamma A x}, lookup Gamma x A -> lookup (TyCons Gamma) x (tyshift A 0)
| lkSTExTyp : forall {Gamma A B x}, lookup Gamma x A -> lookup (ExTypCons Gamma B) x (tyshift A 0).

Inductive lookupTyVar : env -> nat -> Prop :=
| lktvZ : forall {Gamma}, lookupTyVar (TyCons Gamma) 0
| lktvSTB : forall {Gamma A x}, lookupTyVar Gamma x -> lookupTyVar (TBCons Gamma A) x
| lktvSTy : forall {Gamma x}, lookupTyVar Gamma x -> lookupTyVar (TyCons Gamma) (S x)
| lktvSTExTyp : forall {Gamma A x}, lookupTyVar Gamma x -> lookupTyVar (ExTypCons Gamma A) (S x)
| lktvSTEx : forall {Gamma x}, lookupTyVar Gamma x -> lookupTyVar (ExCons Gamma) (S x)
| lktvSSep : forall {Gamma x}, lookupTyVar Gamma x -> lookupTyVar (SepCons Gamma) x.

Inductive lookupExVar : env -> nat -> Prop :=
| lkexZ : forall {Gamma}, lookupExVar (ExCons Gamma) 0
| lkexSTB : forall {Gamma A x}, lookupExVar Gamma x -> lookupExVar (TBCons Gamma A) x
| lkexSTy : forall {Gamma x}, lookupExVar Gamma x -> lookupExVar (TyCons Gamma) (S x)
| lkexSTEx : forall {Gamma x}, lookupExVar Gamma x -> lookupExVar (ExCons Gamma) (S x)
| lkexSTExTyp : forall {Gamma A x}, lookupExVar Gamma x -> lookupExVar (ExTypCons Gamma A) (S x)
| lkexSSep : forall {Gamma x}, lookupExVar Gamma x -> lookupExVar (SepCons Gamma) x.

Inductive lookupExTyp : env -> nat -> type -> Prop :=
| lkextZ : forall {Gamma A},
    lookupExTyp (ExTypCons Gamma A) 0 (tyshift A 0)
| lkextSTy : forall {Gamma A x},
    lookupExTyp Gamma x A ->
    lookupExTyp (TyCons Gamma) (S x) (tyshift A 0)
| lkextSTEx : forall {Gamma A x},
    lookupExTyp Gamma x A ->
    lookupExTyp (ExCons Gamma) (S x) (tyshift A 0)
| lkextSTExTyp : forall {Gamma A B x},
    lookupExTyp Gamma x A ->
    lookupExTyp (ExTypCons Gamma B) (S x) (tyshift A 0)
| lkextSTB : forall {Gamma A x},
    lookupExTyp Gamma x A ->
    lookupExTyp (TBCons Gamma A) x (tyshift A 0).

Inductive lookupExTyp' : env -> nat -> Prop :=
| lkextZ' : forall {Gamma A},
    lookupExTyp' (ExTypCons Gamma A) 0
| lkextSTy' : forall {Gamma x},
    lookupExTyp' Gamma x ->
    lookupExTyp' (TyCons Gamma) (S x)
| lkextSTEx' : forall {Gamma x},
    lookupExTyp' Gamma x ->
    lookupExTyp' (ExCons Gamma) (S x)
| lkextSTExTyp' : forall {Gamma B x},
    lookupExTyp' Gamma x ->
    lookupExTyp' (ExTypCons Gamma B) (S x)
| lkextSTB' : forall {Gamma A x},
    lookupExTyp' Gamma x ->
    lookupExTyp' (TBCons Gamma A) x.

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

Inductive RegularType : env -> type -> Prop :=
| RInt : forall {Gamma}, RegularType Gamma Int
| RTVar : forall {Gamma n},
    lookupTyVar Gamma n ->
    RegularType Gamma (TVar n)
| RArr : forall {Gamma A B},
    RegularType Gamma A ->
    RegularType Gamma B ->
    RegularType Gamma (Arr A B)
| RFall : forall {Gamma A},
    RegularType (TyCons Gamma) A ->
    RegularType Gamma (Fall A)
.

Inductive RegularEnv : env -> Prop :=
| RegEmpty : RegularEnv Empty
| RegTBCons : forall {Gamma A},
    RegularEnv Gamma ->
    RegularType Gamma A ->
    RegularEnv (TBCons Gamma A)
| RegTyCons : forall {Gamma},
    RegularEnv Gamma ->
    RegularEnv (TyCons Gamma)
| RegExCons : forall {Gamma},
    RegularEnv Gamma ->
    RegularEnv (ExCons Gamma)
| RegExTypCons : forall {Gamma A},
    RegularEnv Gamma ->
    RegularType Gamma A ->
    RegularEnv (ExTypCons Gamma A)
| RegSepCons : forall {Gamma},
    RegularEnv Gamma ->
    RegularEnv (SepCons Gamma)
.

Inductive TRegularEnv : env -> Prop :=
| TRegEmpty : TRegularEnv Empty
| TRegTBCons : forall {Gamma A},
    TRegularEnv Gamma ->
    RegularType Gamma A ->
    TRegularEnv (TBCons Gamma A)
| TRegTyCons : forall {Gamma},
    TRegularEnv Gamma ->
    TRegularEnv (TyCons Gamma)
| TRegExCons : forall {Gamma},
    TRegularEnv Gamma ->
    TRegularEnv (ExCons Gamma)
| TRegExTypCons : forall {Gamma A},
    TRegularEnv Gamma ->
    RegularType Gamma A ->
    TRegularEnv (ExTypCons Gamma A)
.

Inductive SRegularEnv : env -> Prop :=
| SRegEmpty : forall {Gamma}, TRegularEnv Gamma -> SRegularEnv (SepCons Gamma)
| SRegTyCons : forall {Gamma},
    SRegularEnv Gamma ->
    SRegularEnv (TyCons Gamma)
| SRegExCons : forall {Gamma},
    SRegularEnv Gamma ->
    SRegularEnv (ExCons Gamma)
| SRegExTypCons : forall {Gamma A},
    SRegularEnv Gamma ->
    RegularType Gamma A ->
    SRegularEnv (ExTypCons Gamma A)
.

Inductive substEnv : type -> nat -> env -> env -> Prop :=
| sEnvExZ : forall {A A' Gamma},
    RegularType Gamma A ->
    SRegularEnv Gamma ->
    A' = tyshift A 0 ->
    substEnv A' 0 (ExCons Gamma) (ExTypCons Gamma A)
| sEnvExS : forall {k A A' Gamma Gamma'},
    substEnv A k Gamma Gamma' ->
    A' = tyshift A 0 ->
    substEnv A' (S k) (ExCons Gamma) (ExCons Gamma')
| sEnvTy : forall {k A A' Gamma Gamma'},
    substEnv A k Gamma Gamma' ->
    A' = tyshift A 0 ->
    substEnv A' (S k) (TyCons Gamma) (TyCons Gamma')
| sEnvExTyp : forall {k A A' B Gamma Gamma'},
    substEnv A k Gamma Gamma' ->
    A' = tyshift A 0 ->
    RegularType Gamma B ->
    substEnv A' (S k) (ExTypCons Gamma B) (ExTypCons Gamma' B)
.

Inductive polar : Set :=
| Pos : polar
| Neg : polar.

Definition neg (p : polar) : polar :=
  match p with
  | Pos => Neg
  | Neg => Pos
  end.

Inductive open : env -> type -> Prop :=
| oExVar : forall {Δ x},
    lookupExVar Δ x ->
    open Δ (TVar x)
| oArrL : forall {Δ A B},
    open Δ A ->
    open Δ (Arr A B)
| oArrR : forall {Δ A B},
    open Δ B ->
    open Δ (Arr A B)
| oFall : forall {Δ A},
    open (TyCons Δ) A ->
    open Δ (Fall A)
.

Inductive close : env -> type -> Prop :=
| cInt : forall Δ, close Δ Int
| cTVar : forall {Δ x},
    lookupTyVar Δ x ->
    close Δ (TVar x)
| cExTyp : forall {Δ x},
    lookupExTyp' Δ x ->
    close Δ (TVar x) 
| cArr : forall {Δ A B},
    close Δ A ->
    close Δ B ->
    close Δ (Arr A B)
| cFall : forall {Δ A},
    close (TyCons Δ) A ->
    close Δ (Fall A)
.
