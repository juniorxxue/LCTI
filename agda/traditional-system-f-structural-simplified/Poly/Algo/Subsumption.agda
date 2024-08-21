module Poly.Algo.Subsumption where

open import Poly.Common
open import Poly.Algo
open import Poly.Algo.Properties

postulate
  ≤strengthen0 : ∀ {Γ : Env n m} {Σ A B}
    → Γ , A ⊢ B ≤ ↑Σ #0 Σ
    → Γ ⊢ B ≤ Σ
  ≤weaken0 : ∀ {Γ : Env n m} {Σ A B}
    → Γ ⊢ B ≤ Σ
    → Γ , A ⊢ B ≤ ↑Σ #0 Σ
  Σspl-weaken0 : ∀ {Σ : Context n m} {a̅}
    → ⟦ Σ ⟧⇒⟦ a̅ , □ ⟧
    → ⟦ ↑Σ0 Σ ⟧⇒⟦ up0 a̅ , □ ⟧

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
  ⊕-weaken0 : ∀ {Σ : Context n m} {es Σ'}
    → es ⊕ Σ' := Σ
    → (up0 es) ⊕ (↑Σ0 Σ') := ↑Σ0 Σ


subsumption : ∀ {Γ : Env n m} {Σ Σ' Σ'' A a̅ e}
  → Γ ⊢ Σ ⇒ e ⇒ A
  → ⟦ Σ ⟧⇒⟦ a̅ , □ ⟧ 
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
... | r = s-arr (≤strengthen0 r) (subsumption0 ⊢e s-refl)
⊢to≤ (⊢sub ⊢e ¬□ gc s) = s
⊢to≤ (⊢tabs₁ ⊢e) = s-empty
⊢to≤ (⊢tapp ⊢e x) with ⊢to≤ ⊢e
... | s-∀-t x₁ r rewrite subst-unique x x₁ = r

-- the proof of subsumption follows the side-condition in subsumption rule
-- 1) we case analysis on the empty/non-empty of the context
-- 2) we case analysis on the generic consumer/non-generic consumer of the expression
-- for non-empty gc cases: subsumption rule applies
-- for others: induction hypothesis applies

-- empty
subsumption {Σ' = □} ⊢e none-□ ⊕nil s-empty = ⊢e
-- repetitions 1
subsumption {Σ' = τ _} ⊢lit none-□ ⊕nil s-refl = ⊢sub ⊢lit ne-τ gc-i s-refl
subsumption {Σ' = τ _} (⊢var x∈Γ) none-□ ⊕nil s-refl = ⊢sub (⊢var x∈Γ) ne-τ gc-var s-refl
subsumption {Σ' = τ _} (⊢ann ⊢e) none-□ ⊕nil s-refl = ⊢sub (⊢ann ⊢e) ne-τ gc-ann s-refl
subsumption {Σ' = τ _} (⊢app ⊢e) none-□ ⊕nil s-refl with ⊢to≤ ⊢e
... | s-arr s-empty ⊢e' = ⊢app (subsumption ⊢e (have-e none-□) (⊕cons-e ⊕nil) (s-arr s-refl ⊢e'))
subsumption {Σ' = τ _} (⊢tabs₁ ⊢e) none-□ ⊕nil s-refl = ⊢sub (⊢tabs₁ ⊢e) ne-τ gc-tlam s-refl
subsumption {Σ' = τ _} (⊢tapp ⊢e st) none-□ ⊕nil s-refl with ⊢to≤ ⊢e
... | s-∀-t st' s-empty rewrite subst-unique st st' =
  ⊢tapp (subsumption ⊢e (have-t none-□) (⊕cons-t ⊕nil) (s-∀-t st (helper (subst-unique st st')))) st'
    where -- idk why the rewrite didn't work here
      helper : ∀ {Γ : Env n m} {A B}
        → A ≡ B
        → Γ ⊢ A ≤ (τ B)
      helper eq rewrite eq = s-refl
-- repetition 2
subsumption {Σ' = [ e ]↝ Σ'} (⊢var x∈Γ) spl newΣ s = ⊢sub (⊢var x∈Γ) ne-app gc-var s
subsumption {Σ' = [ e ]↝ Σ'} (⊢ann ⊢e) spl newΣ s = ⊢sub (⊢ann ⊢e) ne-app gc-ann s
subsumption {Σ' = [ e ]↝ Σ'} (⊢app ⊢e) spl newΣ s with ⊢to≤ ⊢e
... | s-arr r x = ⊢app (subsumption ⊢e (have-e spl) (⊕cons-e newΣ) (s-arr s x))
subsumption {Σ' = [ _ ]↝ Σ'} (⊢lam₂ ⊢e ⊢e₁) (have-e spl) (⊕cons-e newΣ) (s-arr s x) =
  ⊢lam₂ ⊢e (subsumption ⊢e₁ (Σspl-weaken0 spl) (⊕-weaken0 newΣ) (≤weaken0 s)) -- two weakening
subsumption {Σ' = [ e ]↝ Σ'} (⊢sub ⊢e ¬□ gc s₁) spl newΣ s = ⊢sub ⊢e ne-app gc s
subsumption {Σ' = [ e ]↝ Σ'} (⊢tapp ⊢e st) spl newΣ s with ⊢to≤ ⊢e
... | s-∀-t st' r rewrite subst-unique st st' =
  ⊢tapp (subsumption ⊢e (have-t spl) (⊕cons-t newΣ) (s-∀-t st' s)) st' -- more thinking
-- repetition 3
subsumption {Σ' = ⟦ _ ⟧↝ Σ'} (⊢var x∈Γ) spl newΣ s = ⊢sub (⊢var x∈Γ) ne-tapp gc-var s
subsumption {Σ' = ⟦ _ ⟧↝ Σ'} (⊢ann ⊢e) spl newΣ s = ⊢sub (⊢ann ⊢e) ne-tapp gc-ann s
subsumption {Σ' = ⟦ _ ⟧↝ Σ'} (⊢app ⊢e) spl newΣ s with ⊢to≤ ⊢e
... | s-arr r x = ⊢app (subsumption ⊢e (have-e spl) (⊕cons-e newΣ) (s-arr s x))
subsumption {Σ' = ⟦ _ ⟧↝ Σ'} (⊢sub ⊢e ¬□ gc s₁) spl newΣ s = ⊢sub ⊢e ne-tapp gc s
subsumption {Σ' = ⟦ _ ⟧↝ Σ'} (⊢tabs₁ ⊢e) spl newΣ s = ⊢sub (⊢tabs₁ ⊢e) ne-tapp gc-tlam s
subsumption {Σ' = ⟦ _ ⟧↝ Σ'} (⊢tapp ⊢e st) spl newΣ s with ⊢to≤ ⊢e
... | s-∀-t st' r = ⊢tapp (subsumption ⊢e (have-t spl) (⊕cons-t newΣ) (s-∀-t st s)) st


----------------------------------------------------------------------
--+                             Check                              +--
----------------------------------------------------------------------

-- if the context is a full type, then the inferred type should be same with the context
⊢context-full-type : ∀ {Γ : Env n m} {e A B}
  → Γ ⊢ τ A ⇒ e ⇒ B
  → A ≡ B
⊢context-full-type ⊢e with ⊢to≤ ⊢e
... | s-refl = refl
