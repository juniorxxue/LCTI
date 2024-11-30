module Implicit.Algo.Properties.Extension where

open import Implicit.Language
open import Implicit.Algo.Base

⊆-refl : ∀ {n m} {Ψ : SEnv n m}
  → Ψ ⊆ Ψ
⊆-refl {Ψ = ∅} = base
⊆-refl {Ψ = Ψ , A} = var ⊆-refl
⊆-refl {Ψ = Ψ ,∙} = uvar ⊆-refl
⊆-refl {Ψ = Ψ ,^} = evar ⊆-refl
⊆-refl {Ψ = Ψ ,= A} = svar ⊆-refl

⊆-trans : ∀ {n m} {Ψ Ψ' Ψ'' : SEnv n m}
  → Ψ ⊆ Ψ'
  → Ψ' ⊆ Ψ''
  → Ψ ⊆ Ψ''
⊆-trans base base = base
⊆-trans (uvar ⊆1) (uvar ⊆2) = uvar (⊆-trans ⊆1 ⊆2)
⊆-trans (var ⊆1) (var ⊆2) = var (⊆-trans ⊆1 ⊆2)
⊆-trans (evar ⊆1) (evar ⊆2) = evar (⊆-trans ⊆1 ⊆2)
⊆-trans (evar ⊆1) (evar-sol ⊆2) = evar-sol (⊆-trans ⊆1 ⊆2)
⊆-trans (evar-sol ⊆1) (svar ⊆2) = evar-sol (⊆-trans ⊆1 ⊆2)
⊆-trans (svar ⊆1) (svar ⊆2) = svar (⊆-trans ⊆1 ⊆2)

⟹-⊆ : ∀ {Ψ Ψ' : SEnv n m} {A X} 
  → [ A / X ] Ψ ⟹ Ψ'
  → Ψ ⊆ Ψ'
⟹-⊆ (⟹^0 sf) = evar-sol ⊆-refl
⟹-⊆ (⟹,S s) = var (⟹-⊆ s)
⟹-⊆ (⟹^S x s) = evar (⟹-⊆ x)
⟹-⊆ (⟹∙S x s) = uvar (⟹-⊆ x)
⟹-⊆ (⟹=S up s) = svar (⟹-⊆ s)  

s⁺-⊆ : ∀ {Ψ Ψ' : SEnv n m} {A B Σ}
  → Ψ ⊢ A ≤⁺ Σ ⊣ Ψ' ↪ B
  → Ψ ⊆ Ψ'
s⁻-⊆ : ∀ {Ψ Ψ' : SEnv n m} {A B Σ}
  → Ψ ⊢ A ≤⁻ Σ ⊣ Ψ' ↪ B
  → Ψ ⊆ Ψ'

s⁺-⊆ s⁺-int = ⊆-refl
s⁺-⊆ (s⁺-empty cloA) = ⊆-refl
s⁺-⊆ (s⁺-var cloX) = ⊆-refl
s⁺-⊆ (s⁺-ex-l^ cloA x-in inst) = ⟹-⊆ inst
s⁺-⊆ (s⁺-ex-l= cloA x-in s) = s⁺-⊆ s
s⁺-⊆ (s⁺-ex-r= cloA x-in s) = s⁺-⊆ s
s⁺-⊆ (s⁺-arr cloC cloD s s₁) = ⊆-trans (s⁻-⊆ s) (s⁺-⊆ s₁)
s⁺-⊆ (s⁺-term-c cloA cloΣ ⊢e s) = s⁺-⊆ s
s⁺-⊆ (s⁺-term-o opnA cloΣ ⊢e s s₁) = ⊆-trans (s⁻-⊆ s) (s⁺-⊆ s₁)
s⁺-⊆ (s⁺-∀ cloB s) with s⁺-⊆ s
... | uvar r = r
s⁺-⊆ (s⁺-∀l cloΣ s upᶜ upᵉ st₁ st₂) with s⁺-⊆ s
... | evar-sol r = r

s⁻-⊆ s⁻-int = ⊆-refl
s⁻-⊆ (s⁻-var cloX) = ⊆-refl
s⁻-⊆ (s⁻-ex-r^ cloA x-in inst) = ⟹-⊆ inst
s⁻-⊆ (s⁻-ex-l= cloA x-in s) = s⁻-⊆ s
s⁻-⊆ (s⁻-ex-r= cloA x-in s) = s⁻-⊆ s
s⁻-⊆ (s⁻-arr cloA cloB s s₁) = ⊆-trans (s⁺-⊆ s) (s⁻-⊆ s₁)
s⁻-⊆ (s⁻-∀ cloA s) with s⁻-⊆ s
... | uvar r = r

