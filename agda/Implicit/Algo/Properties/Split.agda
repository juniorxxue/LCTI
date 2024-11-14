module Implicit.Algo.Properties.Split where

open import Implicit.Language
open import Implicit.Algo.Base

spl-deterministic : ∀ {Σ : Context n m} {A A₁ A₂ Σ₁ Σ₂}
  → ⟦ Σ , A ⟧→s⟦ Σ₁ ,  A₁ ⟧
  → ⟦ Σ , A ⟧→s⟦ Σ₂ ,  A₂ ⟧
  → Σ₁ ≡ Σ₂ × A₁ ≡ A₂
spl-deterministic none-□ none-□ = ⟨ refl , refl ⟩  
spl-deterministic none-τ none-τ = ⟨ refl , refl ⟩
spl-deterministic (have-e spl1) (have-e spl2) = spl-deterministic spl1 spl2
