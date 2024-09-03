module Implicit.Algo.Subsumption where

open import Implicit.Common
open import Implicit.Algo

infix 4 ⟦_⟧⇒⟦_,_⟧

data ⟦_⟧⇒⟦_,_⟧ : Context n m → Apps n m → Context n m → Set where

  none-□ :
      ⟦ (Context n m ∋⦂ □) ⟧⇒⟦ nil , □ ⟧

  none-τ : ∀ {A}
    → ⟦ (Context n m ∋⦂ τ A) ⟧⇒⟦ nil , τ A ⟧

  have-e : ∀ {Σ Σ' : Context n m} {e es}
    → ⟦ Σ ⟧⇒⟦ es , Σ' ⟧
    → ⟦ [ e ]↝ Σ ⟧⇒⟦ e ∷a es , Σ' ⟧

  have-t : ∀ {Σ Σ' : Context n m} {es A}
    → ⟦ Σ ⟧⇒⟦ es , Σ' ⟧
    → ⟦ ⟦ A ⟧↝ Σ ⟧⇒⟦ A ∷t es , Σ' ⟧

infix 4 _⊕_:=_

data _⊕_:=_ : Apps n m → Context n m → Context n m → Set where

  ⊕nil : ∀ {Σ : Context n m}
    → nil ⊕ Σ := Σ

  ⊕cons-e : ∀ {Σ : Context n m} {e a̅ Σ'}
    → a̅ ⊕ Σ := Σ'
    → (e ∷a a̅) ⊕ Σ := [ e ]↝ Σ'

  ⊕cons-t : ∀ {Σ : Context n m} {A a̅ Σ'}
    → a̅ ⊕ Σ := Σ'
    → (A ∷t a̅) ⊕ Σ := ⟦ A ⟧↝ Σ'

postulate
  subsumption0 : ∀ {Γ : Env n m} {Ψ Σ e A A'}
    → Γ ⊢ □ ⇒ e ⇒ A
    → 𝕓 Γ ⊢ A ≤ Σ ⊣ Ψ ↪ A'
    → Γ ⊢ Σ ⇒ e ⇒ A'

subsumption : ∀ {Γ : Env n m} {Σ Σ' Σ'' Ψ e A A' a̅}
  → Γ ⊢ Σ ⇒ e ⇒ A
  → ⟦ Σ ⟧⇒⟦ a̅ , □ ⟧
  → a̅ ⊕ Σ'' := Σ'
  → 𝕓 Γ ⊢ A ≤ Σ'' ⊣ Ψ ↪ A'
  → Γ ⊢ Σ' ⇒ e ⇒ A'


