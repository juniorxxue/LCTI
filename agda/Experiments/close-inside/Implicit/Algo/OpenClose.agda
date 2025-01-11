module Implicit.Algo.OpenClose where

open import Implicit.Language
open import Implicit.Algo.Syntax
open import Implicit.Algo.Lookup

-- an algorithmic version to define closedness and openness
-- however, it could work for defining a specification around k ε A and and Ψ ⊢^ k

infix 3 _⊢cᶜ_
data _⊢cᶜ_ : Env n m → Context n m → Set where
  ⊢c-empty : Γ ⊢cᶜ □
  ⊢c-τ : (cloA : Γ ⊢c A) → Γ ⊢cᶜ (τ A)
  ⊢c-term : (cloe : Γ ⊢cᵉ e) → Γ ⊢cᶜ Σ → Γ ⊢cᶜ [ e ]↝ Σ -- we may add conditions onto `e` later

infix 3 _⊢oᶜ_
data _⊢oᶜ_ : Env n m → Context n m → Set where
  ⊢o-τ : Γ ⊢o A → Γ ⊢oᶜ (τ A)
  ⊢o-term : Γ ⊢oᶜ Σ → Γ ⊢oᶜ [ e ]↝ Σ -- we may add conditions onto `e` later

