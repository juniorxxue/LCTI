module Implicit.Algo.Properties.Id where

open import Implicit.Language
open import Implicit.Algo.Base
open import Implicit.Algo.Properties.Split

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
... | case-τ spl' refl with sspl-unique spl spl'
... | ⟨ refl , refl ⟩ = refl
≤id' s spl | case-□ spl' with sspl-unique spl spl'
... | ()

⊢id (⊢app ⊢e) spl = ⊢id ⊢e (have-e spl)
⊢id (⊢lam₁ ⊢e) none-τ rewrite ⊢id ⊢e none-τ = refl
⊢id (⊢lam₂ ⊢e upc ⊢e₁) (have-e spl) = ⊢id ⊢e₁ {!!}
⊢id (⊢sub ⊢e ne gc s) spl = ≤id' s (spl→sspl spl)

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
≤id (s-∀l {B = B} s st₁ st₂ upc upe) with ≤id s
... | case-τ spl refl = case-τ (sspl-↑-st spl {!!} {!!} (st-arr upc upe) {!!}) refl
... | case-□ spl = {!!}

-- corollaries
⊢id0 : ∀ {Γ : Env n m} {e A B}
  → Γ ⊢ τ B ⇒ e ⇒ A
  → B ≡ A
⊢id0 ⊢e = ⊢id ⊢e none-τ

≤id0 : ∀ {Ψ Ψ' : SEnv n m} {A B C}
  → Ψ ⊢ A ≤ τ B ⊣ Ψ' ↪ C
  → B ≡ C
≤id0 s = ≤id' s none-τ  
