module Implicit.Algo.Properties.Shift where

open import Implicit.Language.All
open import Implicit.Algo.Base


↑tmᶜ-total : ∀ (Σ : Context n m) (k)
  → ∃ λ Σ'
  → Σ ↑tmᶜ k ⇘ Σ'
↑tmᶜ-total □ k = ⟨ □ , ↑tmᶜ-□ ⟩
↑tmᶜ-total (τ A) k = ⟨ τ A , ↑tmᶜ-τ ⟩
↑tmᶜ-total ([ e ]↝ Σ) k with ↑tm-total e k | ↑tmᶜ-total Σ k
... | ⟨ e' , up-e ⟩ | ⟨ Σ' , up-Σ ⟩ = ⟨ [ e' ]↝ Σ' , ↑tmᶜ-e up-e up-Σ ⟩

↑tmᶜ0-total : ∀ (Σ : Context n m)
  → ∃ λ Σ'
  → ↑tmᶜ0 Σ ⇘ Σ'
↑tmᶜ0-total Σ = ↑tmᶜ-total Σ #0

↑tmᶜ-unique : Σ ↑tmᶜ k ⇘ Σ₁
            → Σ ↑tmᶜ k ⇘ Σ₂
            → Σ₁ ≡ Σ₂
↑tmᶜ-unique ↑tmᶜ-□ ↑tmᶜ-□ = refl
↑tmᶜ-unique ↑tmᶜ-τ ↑tmᶜ-τ = refl
↑tmᶜ-unique (↑tmᶜ-e up-e up1) (↑tmᶜ-e up-e₁ up2) rewrite ↑tm-unique up-e up-e₁ | ↑tmᶜ-unique up1 up2 = refl

↑tyᶜ-total : ∀ (Σ : Context n m) (k)
  → ∃ λ Σ'
  → Σ ↑tyᶜ k ⇘ Σ'
↑tyᶜ-total □ k = ⟨ □ , ↑tyᶜ-□ ⟩
↑tyᶜ-total (τ A) k with ↑ty-total A k
... | ⟨ A' , upA ⟩ = ⟨ τ A' , ↑tyᶜ-τ upA ⟩
↑tyᶜ-total ([ e ]↝ Σ) k with ↑tyᵉ-total e k | ↑tyᶜ-total Σ k
... | ⟨ e' , upe ⟩ | ⟨ Σ' , upΣ ⟩ = ⟨ [ e' ]↝ Σ' , ↑tyᶜ-e upe upΣ ⟩

↑tyᶜ0-total : ∀ (Σ : Context n m)
  → ∃ λ Σ'
  → ↑tyᶜ0 Σ ⇘ Σ'
↑tyᶜ0-total Σ = ↑tyᶜ-total Σ #0
