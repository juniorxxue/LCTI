module Implicit.Algo.Properties.Extension where

open import Implicit.Language
open import Implicit.Algo.Base

s-⊆ : Γ ⊢ A ⌞ ≤ ⌝ Σ ⊣ Γ' ↪ B
    → Γ ⊆ Γ'
s-⊆ s-int = ⊆-refl
s-⊆ (s-empty clo) = ⊆-refl
s-⊆ s-var = ⊆-refl
s-⊆ (s-ex-l^ x-in inst) = inst-⊆ inst
s-⊆ (s-ex-l= x-in s) = s-⊆ s
s-⊆ (s-ex-r^ x-in inst) = inst-⊆ inst
s-⊆ (s-ex-r= x-in s) = s-⊆ s
s-⊆ (s-arr s s₁) = ⊆-trans (s-⊆ s) (s-⊆ s₁)
s-⊆ (s-term-c ⊢e s) = s-⊆ s
s-⊆ (s-term-o opnA ⊢e s s₁) = ⊆-trans (s-⊆ s) (s-⊆ s₁)
s-⊆ (s-∀ s) with s-⊆ s
... | uvar ind = ind
s-⊆ (s-∀l s upᶜ upᵉ st₁ st₂) with s-⊆ s
... | evar-sol ind = ind

