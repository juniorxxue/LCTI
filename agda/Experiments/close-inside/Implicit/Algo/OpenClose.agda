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

data Polarity (Γ : Env n m) (A : Type m) (Σ : Context n m) : Polar → Set where
  polar-l : (cloΓ : Closed Γ) → (cloA : Γ ⊢c A) → Polarity Γ A Σ ≤⁻
  polar-r : (cloΓ : Closed Γ) → (cloΣ : Γ ⊢cᶜ Σ) → Polarity Γ A Σ ≤⁺

----------------------------------------------------------------------
--+                        inversion lemmas                        +--
----------------------------------------------------------------------

polar-arr-l : Polarity Γ (A `→ B) (τ (C `→ D)) ≤
            → Polarity Γ C (τ A) (⋆ ≤)
polar-arr-l (polar-l cloΓ (⊢c-arr cloA cloA₁)) = polar-r cloΓ (⊢c-τ cloA)
polar-arr-l (polar-r cloΓ (⊢c-τ (⊢c-arr cloA cloA₁))) = polar-l cloΓ cloA

polar-arr-r : Polarity Γ (A `→ B) (τ (C `→ D)) ≤
            → Polarity Γ B (τ D) ≤
polar-arr-r (polar-l cloΓ (⊢c-arr cloA cloA₁)) = polar-l cloΓ cloA₁
polar-arr-r (polar-r cloΓ (⊢c-τ (⊢c-arr cloA cloA₁))) = polar-r cloΓ (⊢c-τ cloA₁)

polar-∀ : Polarity Γ (`∀ A) (τ (`∀ B)) ≤
        → Polarity (Γ ,∙) A (τ B) ≤
polar-∀ (polar-l cloΓ (⊢c-∀ cloA)) = polar-l (clo-S∙ cloΓ) cloA
polar-∀ (polar-r cloΓ (⊢c-τ (⊢c-∀ cloA))) = polar-r (clo-S∙ cloΓ) (⊢c-τ cloA)

polar-tm-r : Polarity Γ (A `→ B) ([ e ]↝ Σ) ≤
           → Polarity Γ B Σ ≤
polar-tm-r (polar-l cloΓ (⊢c-arr cloA cloA₁)) = polar-l cloΓ cloA₁
polar-tm-r (polar-r cloΓ (⊢c-term cloe cloA)) = polar-r cloΓ cloA

polar-in-l : Polarity Γ (‶ X) Σ ≤
           → Γ ∋ X := A
           → Polarity Γ A Σ ≤
polar-in-l (polar-l cloΓ (⊢c-var-∙ inΓ₁)) inΓ = ⊥-elim (∙∈-=∈-false inΓ₁ (:=to= inΓ))
polar-in-l (polar-l cloΓ (⊢c-var-= inΓ₁)) inΓ = polar-l cloΓ (∋=-closed cloΓ inΓ)
polar-in-l (polar-r cloΓ cloΣ) inΓ = polar-r cloΓ cloΣ

polar-in-r : Polarity Γ A (τ (‶ X)) ≤
           → Γ ∋ X := B
           → Polarity Γ A (τ B) ≤
polar-in-r (polar-l cloΓ cloA) inΓ = polar-l cloΓ cloA
polar-in-r (polar-r cloΓ (⊢c-τ cloA)) inΓ = polar-r cloΓ (⊢c-τ (∋=-closed cloΓ inΓ))
