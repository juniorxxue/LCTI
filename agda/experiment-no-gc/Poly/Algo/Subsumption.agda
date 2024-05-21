module Poly.Algo.Subsumption where

open import Poly.Common
open import Poly.Algo

postulate
  subsumption0 : ∀ {Γ : Env n m} {Ψ Σ e A A'}
    → Γ ⊢ □ ⇒ e ⇒ A
    → 𝕓 Γ ⊢ A ≤ Σ ⊣ Ψ ↪ A'
    → Γ ⊢ Σ ⇒ e ⇒ A'
