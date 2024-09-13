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

data Γ-unlike : SEnv n m → Set where

  Z : ∀ {Ψ : SEnv n m} → Γ-unlike (Ψ ,^)
  S, : ∀ {Ψ : SEnv n m} {A} → Γ-unlike Ψ → Γ-unlike (Ψ , A)
  S∙ : ∀ {Ψ : SEnv n m} → Γ-unlike Ψ → Γ-unlike (Ψ ,∙)
  S= : ∀ {Ψ : SEnv n m} {A} → Γ-unlike Ψ → Γ-unlike (Ψ ,= A)


infix 3 _~~_
data _~~_ : SEnv n m → SEnv n m → Set where
  base : ∀ {Ψ : SEnv n m}
    → Γ-like Ψ
    → Ψ ~~ Ψ
  uvar : ∀ {Ψ Ψ' : SEnv n m}
    → Γ-unlike Ψ
    → Ψ ~~ Ψ'
    → Ψ ,∙ ~~ Ψ' ,∙
  var : ∀ {Ψ Ψ' : SEnv n m} {A}
    → Γ-unlike Ψ
    → Ψ ~~ Ψ'
    → Ψ , A ~~ Ψ' , A
  evar : ∀ {Ψ Ψ' : SEnv n m}
    → Γ-unlike Ψ
    → Ψ ~~ Ψ'
    → Ψ ,^ ~~ Ψ' ,^
  evar-sol : ∀ {Ψ Ψ' : SEnv n m} {A}
    → Γ-unlike Ψ
    → Ψ ~~ Ψ'
    → Ψ ,^ ~~ Ψ' ,= A    
  svar : ∀ {Ψ Ψ' : SEnv n m} {A}
    → Γ-unlike Ψ
    → Ψ ~~ Ψ'
    → Ψ ,= A ~~ Ψ' ,= A
  

data Γ-like? : SEnv n m → Set where
  like : ∀ {Ψ : SEnv n m} → Γ-like Ψ → Γ-like? Ψ
  unlike : ∀ {Ψ : SEnv n m} → Γ-unlike Ψ → Γ-like? Ψ

Γ-like-unlike : ∀ (Ψ : SEnv n m)
  → Γ-like? Ψ
Γ-like-unlike ∅ = like Z
Γ-like-unlike (Ψ , A) with Γ-like-unlike Ψ
... | like ev = like (S, ev)
... | unlike ev = unlike (S, ev)
Γ-like-unlike (Ψ ,∙) with Γ-like-unlike Ψ
... | like ev = like (S∙ ev)
... | unlike ev = unlike (S∙ ev)
Γ-like-unlike (Ψ ,^) = unlike Z
Γ-like-unlike (Ψ ,= A) with Γ-like-unlike Ψ
... | like ev = like (S= ev)
... | unlike ev = unlike (S= ev)


~~refl : ∀ {n m} {Ψ : SEnv n m}
  → Ψ ~~ Ψ
~~refl {Ψ = ∅} = base Z
~~refl {Ψ = Ψ , A} = {!!}
~~refl {Ψ = Ψ ,∙} = {!!}
~~refl {Ψ = Ψ ,^} = {!!}
~~refl {Ψ = Ψ ,= A} = {!!}

~~trans : ∀ {n m} {Ψ Ψ' Ψ'' : SEnv n m}
  → Ψ ~~ Ψ'
  → Ψ' ~~ Ψ''
  → Ψ ~~ Ψ''
~~trans ~~1 ~~2 = {!!}

⟹closed : ∀ {Ψ Ψ' : SEnv n m} {A X} 
  → [ A / X ] Ψ ⟹ Ψ'
  → Ψ ~~ Ψ'
⟹closed st = {!!}

s-closed-gen : ∀ {Ψ Ψ' : SEnv n m} {A B Σ}
  → Ψ ⊢ A ≤ Σ ⊣ Ψ' ↪ B
  → Ψ ~~ Ψ'
s-closed-gen s-int = {!!}
s-closed-gen (s-empty p) = {!!}
s-closed-gen s-var = {!!}
s-closed-gen (s-ex-l^ x x₁ x₂) = {!!}
s-closed-gen (s-ex-l= x x₁ s) = {!!}
s-closed-gen (s-ex-r^ x x₁ x₂) = {!!}
s-closed-gen (s-ex-r= x x₁ s) = {!!}
s-closed-gen (s-arr s s₁) = {!!}
s-closed-gen (s-term-c x x₁ x₂ s) = {!!}
s-closed-gen (s-term-o x x₁ s s₁) = {!!}
s-closed-gen (s-∀ s) = {!!}
s-closed-gen (s-∀l-^ s) = {!!}
s-closed-gen (s-∀l-eq s x) = {!!}
s-closed-gen (s-∀-t s x) = {!!}
  
s-closed : ∀ {Ψ : SEnv n m} {Ψ' A B Σ}
  → Γ-like Ψ
  → Ψ ⊢ A ≤ Σ ⊣ Ψ' ↪ B
  → Ψ ≡ Ψ'
s-closed {Ψ = Ψ} gl s with s-closed-gen s
... | base x = refl
s-closed {Ψ = .(_ ,∙)} (S∙ gl) s | uvar x r = {!!}
s-closed {Ψ = .(_ , _)} (S, gl) s | var x r = {!!}
s-closed {Ψ = .(_ ,= _)} (S= gl) s | svar x r = {!!}
