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
⊢to≤ (⊢tabs₁ ⊢e) = s-empty
⊢to≤ (⊢tapp ⊢e) with ⊢to≤ ⊢e
... | s-∀-t ↑Σ₁ s st = {!!}

-- the proof of subsumption follows the side-condition in subsumption rule
-- first we case analysis on the empty/non-empty of the context
-- second we case analysis on the generic consumer/non-generic consumer of the expression
-- for non-empty gc cases: subsumption rule applies
-- for others: induction hypothesis applies

-- empty
subsumption {Σ' = □} ⊢e none-□ ⊕nil s-empty = ⊢e
-- non empty, will repeat the case three times
subsumption {Σ' = τ _} ⊢lit none-□ ⊕nil s = ⊢sub ⊢lit ne-τ gc-i s
subsumption {Σ' = τ _} (⊢var x∈Γ) none-□ ⊕nil s = ⊢sub (⊢var x∈Γ) ne-τ gc-var s
subsumption {Σ' = τ _} (⊢ann ⊢e) none-□ ⊕nil s = ⊢sub (⊢ann ⊢e) ne-τ gc-ann s
subsumption {Σ' = τ _} (⊢app ⊢e) none-□ ⊕nil s with ⊢to≤ ⊢e
... | s-term-c ⊢e' s-empty = ⊢app (subsumption ⊢e (have-e none-□) (⊕cons-a ⊕nil) (s-term-c ⊢e' s))
subsumption {Σ' = τ _} (⊢tabs₁ ⊢e) none-□ ⊕nil s = {!!}
subsumption {Σ' = τ _} (⊢tapp ⊢e) none-□ ⊕nil s with ⊢to≤ ⊢e
... | s-∀-t ↑Σ₁ r st = {!!}


subsumption {Σ' = [ _ ]↝ Σ'} ⊢e spl ch s = {!!}
subsumption {Σ' = ⟦ _ ⟧↝ Σ'} ⊢e spl ch s = {!!}
