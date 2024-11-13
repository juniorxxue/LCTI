{-# OPTIONS --allow-unsolved-metas #-}
module Implicit.Decl.Subst where

open import Implicit.Common
open import Implicit.Decl
open import Implicit.Decl.Properties

----------------------------------------------------------------------
--+                              Roll                              +--
----------------------------------------------------------------------

_▻_ : Term n m → Apps n m → Term n m
e ▻ nil = e
e ▻ (e' ∷a es) = (e · e') ▻ es

size-apps : Apps n m → ℕ
size-apps nil = 0
size-apps (_ ∷a as) = 1 + size-apps as

size-counter : Counter → ℕ
size-counter Z = 0
size-counter ∞ = 1
size-counter (I j) = 1 + size-counter j
size-counter (C j) = 1 + size-counter j

size-counter≥0 : ∀ j
  → 0 ≤ size-counter j
size-counter≥0 Z = z≤n
size-counter≥0 ∞ = z≤n
size-counter≥0 (I j) = z≤n
size-counter≥0 (C j) = z≤n

size-type : Type m → ℕ
size-type Int = 0
size-type (‶ X) = 0
size-type (A `→ B) = 1 + size-type A + size-type B
size-type (`∀ A) = 1 + size-type A

-- a bunch of rewriting lemmas
_+++_ : Apps n m → Apps n m → Apps n m
nil +++ as₂ = as₂
(e ∷a as₁) +++ as₂ = e ∷a (as₁ +++ as₂)

data AppsDes (as : Apps n m) : Set where

  des-app : ∀ x x̅
    → as ≡ x̅ +++ (x ∷a nil)
    → AppsDes as

apps-destruct : ∀ (as : Apps n m)
  → 0 < size-apps as
  → AppsDes as
apps-destruct (x ∷a nil) (s≤s sz) = des-app x nil refl
apps-destruct (x ∷a (y ∷a as)) (s≤s sz) with apps-destruct (y ∷a as) (s≤s z≤n)
... | des-app x' x̅ eq rewrite eq = des-app x' (x ∷a x̅) refl

pattern ⟦_⟧a z = z ∷a nil

rw-apps-gen : ∀ (es : Apps n m) {e es'}
  → e ▻ (es +++ es') ≡ (e ▻ es) ▻ es'
rw-apps-gen nil = refl
rw-apps-gen (x ∷a es) = rw-apps-gen es

rw-apps-a : ∀ (es : Apps n m) e x
  → e ▻ (es +++ ⟦ x ⟧a) ≡ (e ▻ es) · x
rw-apps-a es e x = rw-apps-gen es {e = e} {es' = ⟦ x ⟧a}

up-+++-distri-a : ∀ (x̅ : Apps n m) x
  → up0 (x̅ +++ ⟦ x ⟧a) ≡ (up0 x̅) +++ (up0 ⟦ x ⟧a)
up-+++-distri-a nil x = refl
up-+++-distri-a (x₁ ∷a x̅) x rewrite up-+++-distri-a x̅ x = refl

size-+++-distri : ∀ (x̅ : Apps n m) ys
  → size-apps (x̅ +++ ys) ≡ size-apps x̅ + size-apps ys
size-+++-distri nil ys = refl
size-+++-distri (x ∷a x̅) ys rewrite size-+++-distri x̅ ys = refl

size-apps-+++a : ∀ x (x̅ : Apps n m) k
  → suc (size-apps (x̅ +++ ⟦ x ⟧a)) ≤ suc k
  → suc (size-apps x̅) < suc k
size-apps-+++a x x̅ k (s≤s sz) rewrite size-+++-distri x̅ ⟦ x ⟧a | +-comm 1 (size-apps x̅) = s≤s sz

-- main proof
¬<0→nil : ∀ {e̅ : Apps n m}
  → ¬ 1 ≤ size-apps e̅
  → e̅ ≡ nil
¬<0→nil {e̅ = nil} sz = refl
¬<0→nil {e̅ = x ∷a e̅} sz = ⊥-elim (sz (s≤s z≤n))

subst-case-0 : ∀ {Γ : Env n m} {A B e̅ j e e₁}
  → ¬ 1 ≤ size-apps e̅
  → Γ , A ⊢ j # e ▻ up0 e̅ ⦂ B
  → Γ ⊢ Z # e₁ ⦂ A
  → Γ ⊢ j # ((ƛ e) · e₁) ▻ e̅ ⦂ B
subst-case-0 {e̅ = e̅} sz ⊢1 ⊢2 rewrite ¬<0→nil {e̅ = e̅} sz = ⊢app₂ (⊢lam₂ ⊢1) ⊢2

postulate
  subst-3 : ∀ k₁ k₂ k₃ e̅ {Γ : Env n m} {A B e e₁ j}
    → size-apps e̅ < k₁
    → size-counter j < k₂
    → size-type B < k₃
    → Γ , A ⊢ j # e ▻ up0 e̅ ⦂ B
    → Γ ⊢ Z # e₁ ⦂ A
    → Γ ⊢ j # ((ƛ e) · e₁) ▻ e̅ ⦂ B


subst :  ∀ {Γ A B e e₁ j} (e̅ : Apps n m)
  → Γ , A ⊢ j # e ▻ (up0 e̅) ⦂ B
  → Γ ⊢ Z # e₁ ⦂ A
  → Γ ⊢ j # ((ƛ e) · e₁) ▻ e̅ ⦂ B
subst {B = B} {j = j} e̅ ⊢1 ⊢2 =
  subst-3 (suc (size-apps e̅)) (suc (size-counter j)) (suc (size-type B)) e̅ (s≤s m≤m) (s≤s m≤m) (s≤s m≤m) ⊢1 ⊢2
