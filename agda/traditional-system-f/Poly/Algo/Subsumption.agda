module Poly.Algo.Subsumption where

open import Poly.Common
open import Poly.Algo

postulate
  subsumption0 : ∀ {Γ : Env n m} {Σ e A A'}
    → Γ ⊢ □ ⇒ e ⇒ A
    → Γ ⊢ A ≤ Σ ⊣ Γ ↪ A'
    → Γ ⊢ Σ ⇒ e ⇒ A'
