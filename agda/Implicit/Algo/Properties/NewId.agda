module Implicit.Algo.Properties.NewId where

open import Implicit.Language.All
open import Implicit.Algo.Base
open import Implicit.Algo.Properties.Split
open import Implicit.Algo.Properties.Subst


postulate
   ↑ty-spls : ⟦ Σ , A ⟧→s⟦ τ T , B ⟧
            → ↑tyᶜ0 Σ ⇘ Σ'
            → ↑ty0 A ⇘ A'
            → ∃[ T' ](∃[ B' ](⟦ Σ' , A' ⟧→s⟦ τ T' , B' ⟧ ×
                              ↑ty0 T ⇘ T' ×
                              ↑ty0 B ⇘ B'))

⊢id :
    Γ ⊢ Σ ⇒ e ⇒ A
  → ⟦ Σ , A ⟧→s⟦ τ T , A' ⟧
  → T ≡ A'

≤id+ :
    Γ ⊢ A ⌞ ≤⁺ ⌝ Σ ⊣ Γ' ↪ B
  → ⟦ Σ , B ⟧→s⟦ τ T , B' ⟧
  → T ≡ B'

≤id- :
    Γ ⊢ A ⌞ ≤⁻ ⌝ τ B ⊣ Γ' ↪ C
  → A ≡ C

⊢id (⊢app ⊢e) spl = ⊢id ⊢e (have-e spl)
⊢id (⊢lam₁ ⊢e) none-τ rewrite ⊢id ⊢e none-τ = refl
⊢id (⊢lam₂ ⊢e up-c ⊢e₁) (have-e spl) = _
⊢id (⊢sub ⊢e ne gc cloΣ s) spl = ≤id+ s spl

≤id+ (s-int cloΓ) none-τ = refl
≤id+ (s-var-∙ cloΓ x) none-τ = refl
≤id+ (s-var-= cloΓ x) none-τ = refl
≤id+ (s-ex-typ-l=+ x-in s) none-τ = refl
≤id+ (s-ex-typ-r=+ x-in s) none-τ = refl
≤id+ (s-ex-l^ x-in cloA inst) none-τ = refl
≤id+ (s-ex-l= x-in s) none-τ = refl
≤id+ (s-arr s s₁) none-τ with ≤id- s | ≤id+ s₁ none-τ
... | refl | refl = refl
≤id+ (s-term-c cloA ap ⊢e s) (have-e spl) = ≤id+ s spl
≤id+ (s-term-o opnA ⊢e s s₁) (have-e spl) = ≤id+ s₁ spl
≤id+ (s-∀ s) none-τ with ≤id+ s none-τ
... | refl = refl
≤id+ (s-∀l s upᶜ upᵉ upC upD) spl'@(have-e spl)
  with ⟨ _ , ⟨ _ , ⟨ spl'' , ⟨ up1 , up2 ⟩ ⟩ ⟩ ⟩ ← ↑ty-spls spl' (↑tyᶜ-e upᵉ upᶜ) (↑ty-arr upC upD)
  with refl ← ≤id+ s spl'' = ↑ty-unique-inver up1 up2

≤id- (s-int cloΓ) = refl
≤id- (s-var-∙ cloΓ x) = refl
≤id- (s-var-= cloΓ x) = refl
≤id- (s-ex-typ-l=- x-in s) = refl
≤id- (s-ex-typ-r=- x-in s) = refl
≤id- (s-ex-r^ x-in cloA inst) = refl
≤id- (s-ex-r= x-in s) = refl
≤id- (s-arr s s₁) with ≤id+ s none-τ | ≤id- s₁
... | refl | refl = refl
≤id- (s-∀ s) with ≤id- s
... | refl = refl
