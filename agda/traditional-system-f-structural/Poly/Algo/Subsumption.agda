module Poly.Algo.Subsumption where

open import Poly.Common
open import Poly.Algo

infix 4 _⊕_:=_

data _⊕_:=_ : Apps n m → Context n m → Context n m → Set where

  ⊕nil : ∀ {Σ : Context n m}
    → nil ⊕ Σ := Σ

  ⊕cons-a : ∀ {Σ : Context n m} {e a̅ Σ'}
    → a̅ ⊕ Σ := Σ'
    → (e ∷a a̅) ⊕ Σ := [ e ]↝ Σ'

  ⊕cons-t : ∀ {Σ : Context n m} {A a̅ Σ'}
    → a̅ ⊕ Σ := Σ'
    → (A ∷t a̅) ⊕ Σ := ⟦ A ⟧↝ Σ'


subsumption : ∀ {Γ : Env n m} {Σ Σ' Σ'' A B A' A̅ a̅ e}
  → Γ ⊢ Σ ⇒ e ⇒ A
  → ⟦ Σ , A ⟧→⟦ a̅ , □ , A̅ , B ⟧
  → a̅ ⊕ Σ'' := Σ'
  → Γ ⊢ A ≤ Σ' ⊣ Γ ↪ A'
  → Γ ⊢ Σ' ⇒ e ⇒ A'

⊢to≤ : ∀ {Γ : Env n m} {e Σ A}
  → Γ ⊢ Σ ⇒ e ⇒ A
  → Γ ⊢ A ≤ Σ ⊣ Γ ↪ A
  
subsumption0 : ∀ {Γ : Env n m} {Σ e A A'}
  → Γ ⊢ □ ⇒ e ⇒ A
  → Γ ⊢ A ≤ Σ ⊣ Γ ↪ A'
  → Γ ⊢ Σ ⇒ e ⇒ A'
subsumption0 ⊢e s = subsumption ⊢e none-□ ⊕nil s

⊢to≤ ⊢lit = s-empty
⊢to≤ (⊢var x∈Γ) = s-empty
⊢to≤ (⊢ann ⊢e) = s-empty
⊢to≤ (⊢app ⊢e) with ⊢to≤ ⊢e
... | s-term-c x s = s
⊢to≤ (⊢lam₁ ⊢e) = {!!}
⊢to≤ (⊢lam₂ ⊢e ⊢e₁) = {!!}
⊢to≤ (⊢sub ⊢e x x₁ x₂) = {!!}
⊢to≤ (⊢tabs₁ ⊢e) = {!!}
⊢to≤ (⊢tapp ⊢e) = {!!}

subsumption {Σ = .□} ⊢lit spl chan s = {!!}
subsumption {Σ = .□} (⊢var x∈Γ) spl chan s = {!!}
subsumption {Σ = .□} (⊢ann ⊢e) spl chan s = {!!}
subsumption {Σ = Σ} (⊢app ⊢e) spl chan s = {!!}
subsumption {Σ = .([ _ ]↝ _)} (⊢lam₂ ⊢e ⊢e₁) spl chan s = {!!}
subsumption {Σ = Σ} (⊢sub ⊢e x x₁ x₂) spl chan s = {!!}
subsumption {Σ = .□} (⊢tabs₁ ⊢e) spl chan s = {!!}
subsumption {Σ = Σ} (⊢tapp ⊢e) spl chan s = ⊢tapp {!!}
