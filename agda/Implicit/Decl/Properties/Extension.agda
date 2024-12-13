module Implicit.Decl.Properties.Extension where

open import Implicit.Language
open import Implicit.Decl.Base

private variable
  Γ Δ : Env n m
  A B : Type m
  j : Counter
  e : Term n m

s-⊆-prv : Γ ⊢ j # A ≤ B
    → Γ ⊆ Δ
    → Δ ⊢ j # A ≤ B
s-⊆-prv s-refl ext = s-refl
s-⊆-prv s-int ext = s-int
s-⊆-prv s-var ext = s-var
s-⊆-prv (s-arr₁ s s₁) ext = s-arr₁ (s-⊆-prv s ext) (s-⊆-prv s₁ ext)
s-⊆-prv (s-arr₂ s s₁) ext = s-arr₂ (s-⊆-prv s ext) (s-⊆-prv s₁ ext)
s-⊆-prv (s-arr₃ s) ext = s-arr₃ (s-⊆-prv s ext)
s-⊆-prv (s-∀ s) ext = s-∀ (s-⊆-prv s (uvar ext))
s-⊆-prv (s-∀l s x fd st₁ st₂) ext = s-∀l (s-⊆-prv s (svar ext)) x fd st₁ st₂
s-⊆-prv (s-var-l x s) ext = s-var-l (⊆-in:= x ext) (s-⊆-prv s ext)
s-⊆-prv (s-var-r x s) ext = s-var-r (⊆-in:= x ext) (s-⊆-prv s ext)

t-⊆-prv : Γ ⊢ j # e ⦂ A
    → Γ ⊆ Δ
    → Δ ⊢ j # e ⦂ A
t-⊆-prv ⊢lit ext = ⊢lit
t-⊆-prv (⊢var x) ext = ⊢var (⊆-in⦂ x ext)
t-⊆-prv (⊢ann ⊢e) ext = ⊢ann (t-⊆-prv ⊢e ext)
t-⊆-prv (⊢lam₁ ⊢e) ext = ⊢lam₁ (t-⊆-prv ⊢e (var ext))
t-⊆-prv (⊢lam₂ ⊢e) ext = ⊢lam₂ (t-⊆-prv ⊢e (var ext))
t-⊆-prv (⊢app₁ ⊢e ⊢e₁) ext = ⊢app₁ (t-⊆-prv ⊢e ext) (t-⊆-prv ⊢e₁ ext)
t-⊆-prv (⊢app₂ ⊢e ⊢e₁) ext = ⊢app₂ (t-⊆-prv ⊢e ext) (t-⊆-prv ⊢e₁ ext)
t-⊆-prv (⊢sub ⊢e B≤A j≢Z) ext = ⊢sub (t-⊆-prv ⊢e ext) (s-⊆-prv B≤A ext) j≢Z
t-⊆-prv (⊢tabs ⊢e) ext = ⊢tabs (t-⊆-prv ⊢e (uvar ext))
