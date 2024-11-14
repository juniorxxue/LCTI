module Implicit.Algo.Properties.Id where

open import Implicit.Language
open import Implicit.Algo.Base

data Split : (Σ : Context n m) → (B : Type m) → Set where
  case-τ : ∀ {Σ : Context n m} {B T B'}
    → (spl : ⟦ Σ , B ⟧→s⟦ τ T , B' ⟧)
    → (eq : T ≡ B')
    → Split Σ B
    
  case-□ : ∀ {Σ : Context n m} {B B'}
    → (spl : ⟦ Σ , B ⟧→s⟦ □ , B' ⟧)
    → Split Σ B

⊢id : ∀ {Γ : Env n m } {Σ e A A' T es As}
  → Γ ⊢ Σ ⇒ e ⇒ A
  → ⟦ Σ , A ⟧→⟦ es , τ T , As , A' ⟧
  → T ≡ A'

≤id : ∀ {Ψ Ψ' : SEnv n m} {Σ A B}
  → Ψ ⊢ A ≤ Σ ⊣ Ψ' ↪ B
  → Split Σ B

≤id' : ∀ {Ψ Ψ' : SEnv n m} {Σ A B T B'}
  → Ψ ⊢ A ≤ Σ ⊣ Ψ' ↪ B
  → ⟦ Σ , B ⟧→s⟦ τ T , B' ⟧
  → T ≡ B'
≤id' s spl with ≤id s
... | case-τ spl' refl with spl-deterministic spl spl'
... | ⟨ refl , refl ⟩ = refl
≤id' s spl | case-□ spl' with spl-deterministic spl spl'
... | ()

⊢id (⊢app ⊢e) spl = ⊢id ⊢e (have-e spl)
⊢id (⊢lam₁ ⊢e) none-τ rewrite ⊢id ⊢e none-τ = refl
⊢id (⊢lam₂ ⊢e ⊢e₁) (have-e spl) = ⊢id ⊢e₁ (spl-weaken spl)
⊢id (⊢sub ⊢e ne gc s) spl = ≤id' s (spl-implies-simple spl)


≤id s-int = case-τ none-τ refl
≤id (s-empty p) = case-□ none-□
≤id (s-var is-uni) = case-τ none-τ refl
≤id (s-ex-l^ clo x-in inst) = case-τ none-τ refl
≤id (s-ex-l= clo x-in s) = case-τ none-τ refl
≤id (s-ex-r^ clo x-in inst) = case-τ none-τ refl
≤id (s-ex-r= clo x-in s) = case-τ none-τ refl
≤id (s-arr s s₁) = case-τ none-τ refl
≤id (s-term-c cloA ⊢e s) with ≤id s
... | case-τ spl eq = case-τ (have-e spl) eq
... | case-□ spl = case-□ (have-e spl)
≤id (s-term-o op ⊢e s s₁) with ≤id s₁
... | case-τ spl eq = case-τ (have-e spl) eq
... | case-□ spl = case-□ (have-e spl)
≤id (s-∀ s) with ≤id s
... | case-τ none-τ refl = case-τ none-τ refl
≤id (s-∀l {B = B} s st₁ st₂) with ≤id s
... | case-τ spl refl rewrite sym (st-st st₁) | sym (st-st st₂) = case-τ (spl-↑ty-case' {C = B} spl) refl
... | case-□ spl rewrite sym (st-st st₁) | sym (st-st st₂) = case-□ (spl-↑ty-case' {C = B} spl)


