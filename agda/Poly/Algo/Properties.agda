module Poly.Algo.Properties where

open import Poly.Common
open import Poly.Algo

-- open import Relation.Binary.PropositionalEquality.≡-Reasoning
-- why does it not work?

data Γext : SEnv n m → SEnv n m → SEnv n' m' → SEnv n' m' → Set where
  base : ∀ {Γ : Env n m} {Ψ}
    → Γext (𝕓 Γ) Ψ (𝕓 Γ) Ψ
  uvar : ∀ {Ψ Ψ' : SEnv n m} {Γ : Env n' m'} {Ψ''}
    → Γext Ψ Ψ' (𝕓 Γ) Ψ''
    → Γext (Ψ ,∙) (Ψ' ,∙) (𝕓 Γ) Ψ'' 
  evar : ∀ {Ψ Ψ' : SEnv n m} {Γ : Env n' m'} {Ψ''}
    → Γext Ψ Ψ' (𝕓 Γ) Ψ''
    → Γext (Ψ ,^) (Ψ' ,^) (𝕓 Γ) Ψ''
  svar : ∀ {Ψ Ψ' : SEnv n m} {A} {Γ : Env n' m'} {Ψ''}
    → Γext Ψ Ψ' (𝕓 Γ) Ψ''
    → Γext (Ψ ,^) (Ψ' ,= A) (𝕓 Γ) Ψ''

infix 3 _~~_
data _~~_ : SEnv n m → SEnv n m → Set where
  base : ∀ {Γ : Env n m}
    → 𝕓 Γ ~~ 𝕓 Γ
  uvar : ∀ {Ψ Ψ' : SEnv n m}
    → Ψ ~~ Ψ'
    → Ψ ,∙ ~~ Ψ' ,∙
  evar : ∀ {Ψ Ψ' : SEnv n m}
    → Ψ ~~ Ψ'
    → Ψ ,^ ~~ Ψ' ,^
  evar-sol : ∀ {Ψ Ψ' : SEnv n m} {A}
    → Ψ ~~ Ψ'
    → Ψ ,^ ~~ Ψ' ,= A    
  svar : ∀ {Ψ Ψ' : SEnv n m} {A}
    → Ψ ~~ Ψ'
    → Ψ ,= A ~~ Ψ' ,= A

~~refl : ∀ {n m} {Ψ : SEnv n m}
  → Ψ ~~ Ψ
~~refl {Ψ = 𝕓 Γ} = base
~~refl {Ψ = Ψ ,∙} = uvar ~~refl
~~refl {Ψ = Ψ ,^} = evar ~~refl
~~refl {Ψ = Ψ ,= A} = svar ~~refl

~~trans : ∀ {n m} {Ψ Ψ' Ψ'' : SEnv n m}
  → Ψ ~~ Ψ'
  → Ψ' ~~ Ψ''
  → Ψ ~~ Ψ''
~~trans base base = base
~~trans (uvar ~~1) (uvar ~~2) = uvar (~~trans ~~1 ~~2)
~~trans (evar ~~1) (evar ~~2) = evar (~~trans ~~1 ~~2)
~~trans (evar ~~1) (evar-sol ~~2) = evar-sol (~~trans ~~1 ~~2)
~~trans (evar-sol ~~1) (svar ~~2) = evar-sol (~~trans ~~1 ~~2)
~~trans (svar ~~1) (svar ~~2) = svar (~~trans ~~1 ~~2)

⟹closed : ∀ {Ψ Ψ' : SEnv n m} {A X} 
  → [ A / X ] Ψ ⟹ Ψ'
  → Ψ ~~ Ψ'
⟹closed ⟹^0 = evar-sol ~~refl
⟹closed (⟹^S s) = evar (⟹closed s)
⟹closed (⟹∙S s) = uvar (⟹closed s)
⟹closed (⟹=S s) = svar (⟹closed s)

s-closed-gen : ∀ {Ψ Ψ' : SEnv n m} {A B Σ}
  → Ψ ⊢ A ≤ Σ ⊣ Ψ' ↪ B
  → Ψ ~~ Ψ'
s-closed-gen s-int = ~~refl
s-closed-gen (s-empty p x) = ~~refl
s-closed-gen s-var = ~~refl
s-closed-gen (s-ex-l^ x x₁ x₂) = ⟹closed x₂
s-closed-gen (s-ex-l= x x₁ s) = s-closed-gen s
s-closed-gen (s-ex-r^ x x₁ x₂) = ⟹closed x₂
s-closed-gen (s-ex-r= x x₁ s) = s-closed-gen s
s-closed-gen (s-arr s s₁) = ~~trans (s-closed-gen s) (s-closed-gen s₁)
s-closed-gen (s-term-c x x₁ x₂ s) = s-closed-gen s
s-closed-gen (s-term-o x x₁ s s₁) = ~~trans (s-closed-gen s) (s-closed-gen s₁)
s-closed-gen (s-∀ s) with s-closed-gen s
... | uvar r = r
s-closed-gen (s-∀l-^ s) with s-closed-gen s
... | evar r = r
s-closed-gen (s-∀l-eq s) with s-closed-gen s
... | evar-sol r = r
s-closed-gen (s-∀-t s) with s-closed-gen s
... | svar r = r
  
s-closed : ∀ {Γ : Env n m} {Ψ A B Σ}
  → 𝕓 Γ ⊢ A ≤ Σ ⊣ Ψ ↪ B
  → Ψ ≡ 𝕓 Γ
s-closed s with s-closed-gen s
... | base = refl
