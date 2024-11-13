module Implicit.Algo.Extension where

open import Implicit.Common
open import Implicit.Properties
open import Implicit.Algo


⊆refl : ∀ {n m} {Ψ : SEnv n m}
  → Ψ ⊆ Ψ
⊆refl {Ψ = ∅} = base
⊆refl {Ψ = Ψ , A} = var ⊆refl
⊆refl {Ψ = Ψ ,∙} = uvar ⊆refl
⊆refl {Ψ = Ψ ,^} = evar ⊆refl
⊆refl {Ψ = Ψ ,= A} = svar ⊆refl

⊆trans : ∀ {n m} {Ψ Ψ' Ψ'' : SEnv n m}
  → Ψ ⊆ Ψ'
  → Ψ' ⊆ Ψ''
  → Ψ ⊆ Ψ''
⊆trans base base = base
⊆trans (uvar ⊆1) (uvar ⊆2) = uvar (⊆trans ⊆1 ⊆2)
⊆trans (var ⊆1) (var ⊆2) = var (⊆trans ⊆1 ⊆2)
⊆trans (evar ⊆1) (evar ⊆2) = evar (⊆trans ⊆1 ⊆2)
⊆trans (evar ⊆1) (evar-sol ⊆2) = evar-sol (⊆trans ⊆1 ⊆2)
⊆trans (evar-sol ⊆1) (svar ⊆2) = evar-sol (⊆trans ⊆1 ⊆2)
⊆trans (svar ⊆1) (svar ⊆2) = svar (⊆trans ⊆1 ⊆2)

⟹closed : ∀ {Ψ Ψ' : SEnv n m} {A X} 
  → [ A / X ] Ψ ⟹ Ψ'
  → Ψ ⊆ Ψ'
⟹closed (⟹^0 sf) = evar-sol ⊆refl
⟹closed (⟹,S s) = var (⟹closed s)
⟹closed (⟹^S x s) = evar (⟹closed x)
⟹closed (⟹∙S x s) = uvar (⟹closed x)
⟹closed (⟹=S s) = svar (⟹closed s)  

s-⊆ : ∀ {Ψ Ψ' : SEnv n m} {A B Σ}
  → Ψ ⊢ A ≤ Σ ⊣ Ψ' ↪ B
  → Ψ ⊆ Ψ'
s-⊆ s-int = ⊆refl
s-⊆ (s-empty p) = ⊆refl
s-⊆ (s-var is-uni) = ⊆refl
s-⊆ (s-ex-l^ x x₁ x₂) = ⟹closed x₂
s-⊆ (s-ex-l= x x₁ s) = s-⊆ s
s-⊆ (s-ex-r^ x x₁ x₂) = ⟹closed x₂
s-⊆ (s-ex-r= x x₁ s) = s-⊆ s
s-⊆ (s-arr s s₁) = ⊆trans (s-⊆ s) (s-⊆ s₁)
s-⊆ (s-term-c x x₂ s) = s-⊆ s
s-⊆ (s-term-o op x s s₁) = ⊆trans (s-⊆ s) (s-⊆ s₁)
s-⊆ (s-∀ s) with s-⊆ s
... | uvar r = r
s-⊆ (s-∀l s st st') with s-⊆ s
... | evar-sol r = r

