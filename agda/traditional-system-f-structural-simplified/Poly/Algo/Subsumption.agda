module Poly.Algo.Subsumption where

open import Poly.Common
open import Poly.Algo
open import Poly.Algo.Properties

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


subsumption : ∀ {Γ : Env n m} {Σ Σ' Σ'' A B A̅ a̅ e}
  → Γ ⊢ Σ ⇒ e ⇒ A
  → ⟦ Σ , A ⟧→⟦ a̅ , □ , A̅ , B ⟧
  → a̅ ⊕ Σ'' := Σ'
  → Γ ⊢ A ≤ Σ'
  → Γ ⊢ Σ' ⇒ e ⇒ A

⊢to≤ : ∀ {Γ : Env n m} {e Σ A}
  → Γ ⊢ Σ ⇒ e ⇒ A
  → Γ ⊢ A ≤ Σ
  
subsumption0 : ∀ {Γ : Env n m} {Σ e A}
  → Γ ⊢ □ ⇒ e ⇒ A
  → Γ ⊢ A ≤ Σ
  → Γ ⊢ Σ ⇒ e ⇒ A
subsumption0 ⊢e s = subsumption ⊢e none-□ ⊕nil s

⊢to≤ ⊢lit = s-empty
⊢to≤ (⊢var x∈Γ) = s-empty
⊢to≤ (⊢ann ⊢e) = s-empty
⊢to≤ (⊢app ⊢e) with ⊢to≤ ⊢e
... | s-arr r x = r
⊢to≤ (⊢lam₁ ⊢e) with ⊢to≤ ⊢e
... | s-refl = s-refl
⊢to≤ (⊢lam₂ ⊢e ⊢e₁) with ⊢to≤ ⊢e₁
... | r = s-arr {!!} (subsumption0 ⊢e s-refl)
⊢to≤ (⊢sub ⊢e ¬□ gc s) = s
⊢to≤ (⊢tabs₁ ⊢e) = s-empty
⊢to≤ (⊢tapp ⊢e x) with ⊢to≤ ⊢e
... | s-∀-t x₁ r rewrite subst-unique x x₁ = r

-- the proof of subsumption follows the side-condition in subsumption rule
-- first we case analysis on the empty/non-empty of the context
-- second we case analysis on the generic consumer/non-generic consumer of the expression
-- for non-empty gc cases: subsumption rule applies
-- for others: induction hypothesis applies

-- empty
subsumption ⊢e spl newΣ s = {!!}
