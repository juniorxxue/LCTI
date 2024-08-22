module Poly.Algo.Subsumption where

open import Poly.Common
open import Poly.Algo
open import Poly.Algo.Properties

↑tmGenCon : ∀ {e : Term n m} {k }
  → GenericConsumer e 
  → GenericConsumer (↑tm k e)
↑tmGenCon {e = .(Term _ _ ∋⦂ lit _)} gc-i = gc-i
↑tmGenCon {e = .(Term _ _ ∋⦂ ` _)} gc-var = gc-var
↑tmGenCon {e = .(_ ⦂ _)} gc-ann = gc-ann
↑tmGenCon {e = .(Λ _)} gc-tlam = gc-tlam 

↑ΣnonEmpty : ∀ {Σ : Context n m} {k}
  → NonEmpty Σ
  → NonEmpty (↑Σ k Σ)
↑ΣnonEmpty ne-τ = ne-τ
↑ΣnonEmpty ne-app = ne-app
↑ΣnonEmpty ne-tapp = ne-tapp

↑Σ-comm : ∀ {Σ : Context n m} {j : Fin (1 + n)} {k : Fin (1 + n)}
  → j F≤ k
  → ↑Σ (inject₁ j) (↑Σ k Σ) ≡ ↑Σ (#S k) (↑Σ j Σ)
↑Σ-comm {Σ = □} j≤k = refl
↑Σ-comm {Σ = τ A} j≤k = refl
↑Σ-comm {Σ = [ e ]↝ Σ} j≤k = cong₂ [_]↝_ (↑tm-comm j≤k) (↑Σ-comm j≤k)
↑Σ-comm {Σ = ⟦ A ⟧↝ Σ} j≤k = cong (⟦_⟧↝_ A) (↑Σ-comm j≤k)

↑Σ-comm0 : ∀ {Σ : Context n m} {k}
  → ↑Σ0 (↑Σ k Σ) ≡ ↑Σ (#S k) (↑Σ0 Σ)
↑Σ-comm0 = ↑Σ-comm _≤_.z≤n

≤weaken : ∀ {Γ : Env (1 + n) m} {Σ k A}
  → (Γ /ˣ k) ⊢ A ≤ Σ
  → Γ ⊢ A ≤ ↑Σ k Σ

⊢weaken : ∀ {Γ : Env (1 + n) m} { Σ k e A }
  → (Γ /ˣ k) ⊢ Σ ⇒ e ⇒ A
  → Γ ⊢ ↑Σ k Σ ⇒ ↑tm k e ⇒ A
    
≤weaken s-empty = s-empty
≤weaken s-refl = s-refl
≤weaken (s-arr ≤A ⊢e) = s-arr (≤weaken ≤A) (⊢weaken ⊢e)
≤weaken (s-∀-t st ≤A) = s-∀-t st (≤weaken ≤A)

⊢weaken ⊢lit = ⊢lit
⊢weaken (⊢var x∈Γ) = ⊢var (∈-weaken x∈Γ)
⊢weaken (⊢ann ⊢e) = ⊢ann (⊢weaken ⊢e)
⊢weaken (⊢app ⊢e) = ⊢app (⊢weaken ⊢e)
⊢weaken (⊢lam₁ ⊢e) = ⊢lam₁ (⊢weaken ⊢e)
⊢weaken {Γ = Γ} {k = k} (⊢lam₂ {Σ = Σ} {A} ⊢e ⊢e₁) with ⊢weaken {Γ = Γ , A} { k = #S k} ⊢e₁ 
... | p rewrite (sym (↑Σ-comm0 {Σ = Σ} {k = k})) = ⊢lam₂ (⊢weaken ⊢e) p
⊢weaken (⊢sub ⊢e ¬□ gc s) = ⊢sub (⊢weaken ⊢e) (↑ΣnonEmpty ¬□) (↑tmGenCon gc) (≤weaken s)
⊢weaken (⊢tabs₁ ⊢e) = ⊢tabs₁ (⊢weaken ⊢e)
⊢weaken (⊢tapp ⊢e st) = ⊢tapp (⊢weaken ⊢e) st  

postulate
  ≤strengthen0 : ∀ {Γ : Env n m} {Σ A B}
    → Γ , A ⊢ B ≤ ↑Σ #0 Σ
    → Γ ⊢ B ≤ Σ

≤weaken0 : ∀ {Γ : Env n m} {Σ A B}
  → Γ ⊢ B ≤ Σ
  → Γ , A ⊢ B ≤ ↑Σ #0 Σ
≤weaken0 s = ≤weaken s  
    
Σspl-weaken0 : ∀ {Σ : Context n m} {a̅}
  → ⟦ Σ ⟧⇒⟦ a̅ , □ ⟧
  → ⟦ ↑Σ0 Σ ⟧⇒⟦ up0 a̅ , □ ⟧
Σspl-weaken0 none-□ = none-□
Σspl-weaken0 (have-e s) = have-e (Σspl-weaken0 s)
Σspl-weaken0 (have-t s) = have-t (Σspl-weaken0 s)

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

⊕-weaken0 : ∀ {Σ : Context n m} {es Σ'}
  → es ⊕ Σ' := Σ
  → (up0 es) ⊕ (↑Σ0 Σ') := ↑Σ0 Σ
⊕-weaken0 ⊕nil = ⊕nil
⊕-weaken0 (⊕cons-e x) = ⊕cons-e (⊕-weaken0 x)
⊕-weaken0 (⊕cons-t x) = ⊕cons-t (⊕-weaken0 x)

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
