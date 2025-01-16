module Implicit.Algo.Properties.Id where

open import Implicit.Language
open import Implicit.Algo.Base
open import Implicit.Algo.Properties.Split
open import Implicit.Algo.Properties.Subst

data Split : (Σ : Context n m) → (A : Type m) → Set where
  case-τ :
      (spl : ⟦ Σ , A ⟧→s⟦ τ T , A' ⟧)
    → (eq : T ≡ A')
    → Split Σ A
    
  case-□ :
      (spl : ⟦ Σ , A ⟧→s⟦ □ , A' ⟧)
    → Split Σ A

⊢id :
    Γ ⊢ Σ ⇒ e ⇒ A
  → ⟦ Σ , A ⟧→⟦ e̅ , τ T , A̅ , A' ⟧
  → T ≡ A'

≤id :
    Γ ⊢ A ⌞ ≤ ⌝ Σ ⊣ Γ' ↪ B
  → Split Σ B

≤id' :
    Γ ⊢ A ⌞ ≤ ⌝ Σ ⊣ Γ' ↪ B
  → ⟦ Σ , B ⟧→s⟦ τ T , B' ⟧
  → T ≡ B'
≤id' s spl with ≤id s
... | case-τ spl' refl with sspl-unique spl spl'
... | ⟨ refl , refl ⟩ = refl
≤id' s spl | case-□ spl' with sspl-unique spl spl'
... | ()

⊢id (⊢app ⊢e) spl = ⊢id ⊢e (have-e spl)
⊢id (⊢lam₁ ⊢e) none-τ rewrite ⊢id ⊢e none-τ = refl
⊢id (⊢lam₂ ⊢e upc ⊢e₁) (have-e spl) = let ⟨ _ , ⟨ spl' , _ ⟩ ⟩ = spl-↑tm spl upc
                                      in ⊢id ⊢e₁ spl'
⊢id (⊢sub ⊢e ne gc clo s) spl = ≤id' s (spl→sspl spl)

≤id s-int = case-τ none-τ refl
≤id (s-empty clo) = case-□ none-□
≤id s-var = case-τ none-τ refl
≤id (s-ex-l^ x-in inst) = case-τ none-τ refl
≤id (s-ex-l= x-in s) = case-τ none-τ refl
≤id (s-ex-r^ x-in inst) = case-τ none-τ refl
≤id (s-ex-r= x-in s) = case-τ none-τ refl
≤id (s-arr s s₁) = case-τ none-τ refl
≤id (s-term-c ⊢e s) with ≤id s
... | case-τ spl eq = case-τ (have-e spl) eq
... | case-□ spl = case-□ (have-e spl)
≤id (s-term-o opnA ⊢e s s₁) with ≤id s₁
... | case-τ spl eq = case-τ (have-e spl) eq
... | case-□ spl = case-□ (have-e spl)
≤id (s-∀ s) with ≤id s
... | case-τ none-τ refl = case-τ none-τ refl
≤id (s-∀l {B = B} s upᶜ upᵉ st₁ st₂) with ≤id s
... | case-τ {T = T} spl refl = let ⟨ _ , st' ⟩ = st0-total B T
                                in case-τ (sspl-↑-st spl (term (↑tyᶜ-st upᶜ) (↑tyᵉ-st upᵉ)) (fulltype st') (st-arr st₁ st₂) st') refl
... | case-□ {A' = A'} spl = let ⟨ _ , st' ⟩ = st0-total B A'
                             in case-□ (sspl-↑-st spl (term (↑tyᶜ-st upᶜ) (↑tyᵉ-st upᵉ)) empty (st-arr st₁ st₂) st')

-- corollaries
⊢id0 : Γ ⊢ τ B ⇒ e ⇒ A
     → B ≡ A
⊢id0 ⊢e = ⊢id ⊢e none-τ

≤id0 : Γ ⊢ A ⌞ ≤ ⌝ τ B ⊣ Γ' ↪ C
     → B ≡ C
≤id0 s = ≤id' s none-τ  
