module Implicit.Interm.Properties.Extension where

open import Implicit.Language
open import Implicit.Interm.Base
open import Implicit.Interm.Properties.OpenClose

s-⊆-prv : Γ ⊢ j # A ≤ B
        → Γ ⊆ Δ
        → Δ ⊢ j # A ≤ B
s-⊆-prv (s-refl cloΣ cloA) ext = s-refl (⊆-closed cloΣ ext) (⊆-cloA cloA ext)
s-⊆-prv (s-int cloΓ) ext = s-int (⊆-closed cloΓ ext)
s-⊆-prv (s-var-∙ cloΓ inΓ) ext = s-var-∙ (⊆-closed cloΓ ext) (⊆-in∙ inΓ ext)
s-⊆-prv (s-var-= cloΓ inΓ) ext = s-var-= (⊆-closed cloΓ ext) (⊆-in= inΓ ext)
s-⊆-prv (s-arr₁ s s₁) ext = s-arr₁ (s-⊆-prv s ext) (s-⊆-prv s₁ ext)
s-⊆-prv (s-arr₂ s s₁) ext = s-arr₂ (s-⊆-prv s ext) (s-⊆-prv s₁ ext)
s-⊆-prv (s-arr₃ cloA s) ext = s-arr₃ (⊆-cloA cloA ext) (s-⊆-prv s ext)
s-⊆-prv (s-∀ s) ext = s-∀ (s-⊆-prv s (uvar ext))
s-⊆-prv (s-∀l s ic fd st₁ st₂) ext = s-∀l (s-⊆-prv s (svar ext)) ic fd st₁ st₂
s-⊆-prv (s-var-l inΓ s) ext = s-var-l (⊆-in:= inΓ ext) (s-⊆-prv s ext)
s-⊆-prv (s-var-r inΓ s) ext = s-var-r (⊆-in:= inΓ ext) (s-⊆-prv s ext)

t-⊆-prv : Γ ⊢ j # e ⦂ A
        → Γ ⊆ Δ
        → Δ ⊢ j # e ⦂ A
t-⊆-prv (⊢lit cloΣ) ext = ⊢lit (⊆-closed cloΣ ext)
t-⊆-prv (⊢var cloΣ x∈Γ) ext = ⊢var (⊆-closed cloΣ ext) (⊆-in⦂ x∈Γ ext)
t-⊆-prv (⊢ann ⊢e) ext = ⊢ann (t-⊆-prv ⊢e ext)
t-⊆-prv (⊢lam₁ ⊢e) ext = ⊢lam₁ (t-⊆-prv ⊢e (var ext))
t-⊆-prv (⊢lam₂ ⊢e) ext = ⊢lam₂ (t-⊆-prv ⊢e (var ext))
t-⊆-prv (⊢app₁ ⊢e ⊢e₁) ext = ⊢app₁ (t-⊆-prv ⊢e ext) (t-⊆-prv ⊢e₁ ext)
t-⊆-prv (⊢app₂ ⊢e ⊢e₁) ext = ⊢app₂ (t-⊆-prv ⊢e ext) (t-⊆-prv ⊢e₁ ext)
t-⊆-prv (⊢sub ⊢e B≤A j≢Z) ext = ⊢sub (t-⊆-prv ⊢e ext) (s-⊆-prv B≤A ext) j≢Z
t-⊆-prv (⊢tabs ⊢e) ext = ⊢tabs (t-⊆-prv ⊢e (uvar ext))
