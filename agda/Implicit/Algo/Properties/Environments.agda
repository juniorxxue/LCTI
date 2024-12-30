module Implicit.Algo.Properties.Environments where

open import Implicit.Language
open import Implicit.Algo.Base
open import Implicit.Algo.Properties.Extension
open import Implicit.Algo.Properties.OpenClose


t-⊆-prv : Γ ⊢ Σ ⇒ e ⇒ A
        → Γ ⊆ Δ
        → Closed Δ
        → Δ ⊢ Σ ⇒ e ⇒ A

postulate
  s-⊆-prv : Γ ⊢ A ⌞ ≤ ⌝ Σ ⊣ Γ ↪ B
          → Γ ⊢c A
          → Γ ⊢cᶜ Σ
          → Δ ⊢ A ⌞ ≤ ⌝ Σ ⊣ Δ ↪ B

t-⊆-prv (⊢lit cloΓ) ext cloΔ = ⊢lit cloΔ
t-⊆-prv (⊢var cloΓ x∈Γ) ext cloΔ = ⊢var cloΔ (⊆-in⦂ x∈Γ ext)
t-⊆-prv (⊢ann ⊢e) ext cloΔ = ⊢ann (t-⊆-prv ⊢e ext cloΔ)
t-⊆-prv (⊢app ⊢e) ext cloΔ = ⊢app (t-⊆-prv ⊢e ext cloΔ)
t-⊆-prv ⊢e'@(⊢lam₁ ⊢e) ext cloΔ with ⊢close-τ ⊢e'
... | (⊢c-arr cloA cloB) with t-⊆-prv ⊢e (var ext) (clo-S, cloΔ (⊆-closed cloA ext))
... | ind = ⊢lam₁ ind
t-⊆-prv (⊢lam₂ ⊢e up-c ⊢e₁) ext cloΔ = {!!}
t-⊆-prv (⊢sub ⊢e ne gc cloΣ s) ext cloΔ = ⊢sub (t-⊆-prv ⊢e ext cloΔ) ne gc {!!} (s-⊆-prv s (⊢closeA ⊢e) cloΣ)
t-⊆-prv (⊢tabs ⊢e) ext cloΔ = ⊢tabs (t-⊆-prv ⊢e (uvar ext) (clo-S∙ cloΔ))
