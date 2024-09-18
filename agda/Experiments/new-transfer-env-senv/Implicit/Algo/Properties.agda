module Implicit.Algo.Properties where

open import Implicit.Common
open import Implicit.Algo

-- open import Relation.Binary.PropositionalEquality.≡-Reasoning
-- why does it not work?

data Γ-like : SEnv n m → Set where
  Z : Γ-like ∅
  S, : ∀ {Ψ : SEnv n m} {A}
    → Γ-like Ψ
    → Γ-like (Ψ , A)
  S∙ : ∀ {Ψ : SEnv n m}
    → Γ-like Ψ
    → Γ-like (Ψ ,∙)
  S= : ∀ {Ψ : SEnv n m} {A}
    → Γ-like Ψ
    → Γ-like (Ψ ,= A)


infix 3 _~~_
data _~~_ : SEnv n m → SEnv n m → Set where
  base : ∅ ~~ ∅
  uvar : ∀ {Ψ Ψ' : SEnv n m}
    → Ψ ~~ Ψ'
    → Ψ ,∙ ~~ Ψ' ,∙
  var : ∀ {Ψ Ψ' : SEnv n m} {A}
    → Ψ ~~ Ψ'
    → Ψ , A ~~ Ψ' , A
  evar : ∀ {Ψ Ψ' : SEnv n m}
    → Ψ ~~ Ψ'
    → Ψ ,^ ~~ Ψ' ,^
  evar-sol : ∀ {Ψ Ψ' : SEnv n m} {A}
    → Ψ ~~ Ψ'
    → Ψ ,^ ~~ Ψ' ,= A    
  svar : ∀ {Ψ Ψ' : SEnv n m} {A}
    → Ψ ~~ Ψ'
    → Ψ ,= A ~~ Ψ' ,= A


~~Γ-like : ∀ {Ψ Ψ' : SEnv n m}
  → Γ-like Ψ
  → Ψ ~~ Ψ'
  → Ψ ≡ Ψ'
~~Γ-like gl base = refl
~~Γ-like (S∙ gl) (uvar ~~Ψ) rewrite ~~Γ-like gl ~~Ψ = refl
~~Γ-like (S, gl) (var ~~Ψ) rewrite ~~Γ-like gl ~~Ψ = refl
~~Γ-like (S= gl) (svar ~~Ψ) rewrite ~~Γ-like gl ~~Ψ = refl

~~refl : ∀ {n m} {Ψ : SEnv n m}
  → Ψ ~~ Ψ
~~refl {Ψ = ∅} = base
~~refl {Ψ = Ψ , A} = var ~~refl
~~refl {Ψ = Ψ ,∙} = uvar ~~refl
~~refl {Ψ = Ψ ,^} = evar ~~refl
~~refl {Ψ = Ψ ,= A} = svar ~~refl

~~trans : ∀ {n m} {Ψ Ψ' Ψ'' : SEnv n m}
  → Ψ ~~ Ψ'
  → Ψ' ~~ Ψ''
  → Ψ ~~ Ψ''
~~trans base base = base
~~trans (uvar ~~1) (uvar ~~2) = uvar (~~trans ~~1 ~~2)
~~trans (var ~~1) (var ~~2) = var (~~trans ~~1 ~~2)
~~trans (evar ~~1) (evar ~~2) = evar (~~trans ~~1 ~~2)
~~trans (evar ~~1) (evar-sol ~~2) = evar-sol (~~trans ~~1 ~~2)
~~trans (evar-sol ~~1) (svar ~~2) = evar-sol (~~trans ~~1 ~~2)
~~trans (svar ~~1) (svar ~~2) = svar (~~trans ~~1 ~~2)

⟹closed : ∀ {Ψ Ψ' : SEnv n m} {A X} 
  → [ A / X ] Ψ ⟹ Ψ'
  → Ψ ~~ Ψ'
⟹closed ⟹^0 = evar-sol ~~refl
⟹closed (⟹,S s) = var (⟹closed s)
⟹closed (⟹^S s) = evar (⟹closed s)
⟹closed (⟹∙S s) = uvar (⟹closed s)
⟹closed (⟹=S s) = svar (⟹closed s)  

s-closed-gen : ∀ {Ψ Ψ' : SEnv n m} {A B Σ}
  → Ψ ⊢ A ≤ Σ ⊣ Ψ' ↪ B
  → Ψ ~~ Ψ'
s-closed-gen s-int = ~~refl
s-closed-gen (s-empty p) = ~~refl
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
s-closed-gen (s-∀l-eq s st) with s-closed-gen s
... | evar-sol r = r
s-closed-gen (s-∀-t s st) with s-closed-gen s
... | svar r = r

𝕎-Γ-like : ∀ (Γ : Env n m)
  → Γ-like (𝕎 Γ)
𝕎-Γ-like ∅ = Z
𝕎-Γ-like (Γ , A) = S, (𝕎-Γ-like Γ)
𝕎-Γ-like (Γ ,∙) = S∙ (𝕎-Γ-like Γ)
𝕎-Γ-like (Γ ,= A) = S= (𝕎-Γ-like Γ)
  
s-closed : ∀ {Ψ : SEnv n m} {Γ A B Σ}
  → 𝕎 Γ ⊢ A ≤ Σ ⊣ Ψ ↪ B
  → Ψ ≡ 𝕎 Γ
s-closed {Γ = Γ} s with s-closed-gen s
... | r = sym (~~Γ-like (𝕎-Γ-like Γ) r)

----------------------------------------------------------------------
--+                   when context is full type                    +--
----------------------------------------------------------------------

postulate
  spl-weaken : ∀ {Σ : Context n m} {B Bs A' es T}
    → ⟦ Σ , B ⟧→⟦ es , τ T , Bs , A' ⟧
    → ⟦ ↑Σ0 Σ , B ⟧→⟦ up0 es , τ T , Bs , A' ⟧

⊢id : ∀ {Γ : Env n m } {Σ e A A' T es As}
  → Γ ⊢ Σ ⇒ e ⇒ A
  → ⟦ Σ , A ⟧→⟦ es , τ T , As , A' ⟧
  → T ≡ A'

≤id : ∀ {Ψ Ψ' : SEnv n m} {Σ A B Bs B' es T}
  → Ψ ⊢ A ≤ Σ ⊣ Ψ' ↪ B
  → ⟦ Σ , B ⟧→⟦ es , τ T , Bs , B' ⟧
  → T ≡ B'
  
⊢id (⊢app ⊢e) spl = ⊢id ⊢e (have-e spl)
⊢id (⊢lam₁ ⊢e) none-τ rewrite ⊢id ⊢e none-τ = refl
⊢id (⊢lam₂ ⊢e ⊢e₁) (have-e spl) = ⊢id ⊢e₁ (spl-weaken spl)
⊢id (⊢sub ⊢e x x₁ s) spl = ≤id s spl
⊢id (⊢tapp ⊢e) spl = ⊢id ⊢e (have-t spl)

≤id s-int none-τ = refl
≤id s-var none-τ = refl
≤id (s-ex-l^ clo x-in inst) none-τ = refl
≤id (s-ex-l= clo x-in s) none-τ = refl
≤id (s-ex-r^ clo x-in inst) none-τ = refl
≤id (s-ex-r= clo x-in s) none-τ = refl
≤id (s-arr s s₁) none-τ = refl
≤id (s-term-c cloA cloB ⊢e s) (have-e spl) = ≤id s spl
≤id (s-term-o op ⊢e s s₁) (have-e spl) = ≤id s₁ spl
≤id (s-∀ s) none-τ = cong `∀_ (≤id s none-τ)
≤id (s-∀l-^ s) (have-e spl) with ≤id s (have-e {!!})
... | r = {!!}
≤id (s-∀l-eq s st) (have-e spl) = {!!}
≤id (s-∀-t s st) (have-t spl) = {!≤id s!}
