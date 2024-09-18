module Implicit.Algo.Subsumption where

open import Implicit.Common
open import Implicit.Algo
open import Implicit.Algo.Properties

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
    → 𝕎 Γ ⊢ A ≤ Σ ⊣ Ψ ↪ A'
    → Γ ⊢ Σ ⇒ e ⇒ A'

⊢to≤ : ∀ {Γ : Env n m} {e Σ A}
  → Γ ⊢ Σ ⇒ e ⇒ A
  → 𝕎 Γ ⊢ A ≤ Σ ⊣ 𝕎 Γ ↪ A

subsumption : ∀ {Γ : Env n m} {Σ Σ' Σ'' Ψ e A A' a̅}
  → Γ ⊢ Σ ⇒ e ⇒ A
  → ⟦ Σ ⟧⇒⟦ a̅ , □ ⟧
  → a̅ ⊕ Σ'' := Σ'
  → 𝕎 Γ ⊢ A ≤ Σ'' ⊣ Ψ ↪ A'
  → Γ ⊢ Σ' ⇒ e ⇒ A'

⊢to≤ ⊢lit = s-empty ⊢c-int
⊢to≤ (⊢var x∈Γ) = s-empty {!!}
⊢to≤ (⊢ann ⊢e) = s-empty {!!}
⊢to≤ (⊢app ⊢e) with ⊢to≤ ⊢e
... | s-term-c x x₁ x₂ r = r
... | s-term-o x x₁ r r₁ rewrite s-closed r = r₁
⊢to≤ (⊢lam₁ ⊢e) with ⊢to≤ ⊢e
... | s = {!!}
⊢to≤ (⊢lam₂ ⊢e ⊢e₁) = {!!}
⊢to≤ (⊢sub ⊢e x x₁ x₂) = {!!}
⊢to≤ (⊢tabs₁ ⊢e) = {!!}
⊢to≤ (⊢tapp ⊢e) = {!!}

subsumption ⊢lit spl ch s = {!!}
subsumption (⊢var x∈Γ) spl ch s = {!!}
subsumption (⊢ann ⊢e) spl ch s = {!!}
subsumption (⊢app ⊢e) spl ch s = {!!}
subsumption (⊢lam₂ ⊢e ⊢e₁) spl ch s = {!!}
subsumption (⊢sub ⊢e x x₁ x₂) spl ch s = {!!}
subsumption (⊢tabs₁ ⊢e) spl ch s = {!!}
subsumption (⊢tapp ⊢e) spl ch s = {!!}


