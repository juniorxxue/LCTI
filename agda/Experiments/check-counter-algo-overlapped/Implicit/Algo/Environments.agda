module Implicit.Algo.Environments where

open import Implicit.Common
open import Implicit.Properties
open import Implicit.Algo

private variable
  Ψ Ψ' : SEnv n m
  A B C : Type m
  k : Fin m
  Σ : Context n m

inst-in : ∀ {X}
  → [ A / X ] Ψ ⟹ Ψ'
  → X := A ∈ Ψ'
inst-in (⟹^0 st) = Z st
inst-in (⟹^S ist) = S^ (inst-in ist)
inst-in (⟹∙S ist) = S∙ (inst-in ist)
inst-in (⟹,S ist) = S, (inst-in ist)
inst-in (⟹=S ist) = S= (inst-in ist)

-- Ψ ⊢ k ^∈ A
-- A contains type variable k, which is unsolved ex-var in Ψ
infix 3 _⊢_^∈_
data _⊢_^∈_ : SEnv n m → Fin m → Type m → Set where
  ^in-var :
      k ^∈ Ψ
    → Ψ ⊢ k ^∈ (‶ k)
  ^in-arr-l :
      Ψ ⊢ k ^∈ A
    → Ψ ⊢ k ^∈ A `→ B
  ^in-arr-r :
      Ψ ⊢ k ^∈ B
    → Ψ ⊢ k ^∈ A `→ B
  ^in-∀ :
      Ψ ,∙ ⊢ #S k ^∈ A
    → Ψ ⊢ k ^∈ `∀ A

infix 3 _⊢_:=_∈_
data _⊢_:=_∈_ : SEnv n m → Fin m → Type m → Type m → Set where
  ^:=-var :
      k := C ∈ Ψ
    → Ψ ⊢ k := C ∈ (‶ k)
  ^:=-arr-l :
      Ψ ⊢ k := C ∈ A
    → Ψ ⊢ k := C ∈ A `→ B
  ^:=-arr-r :
      Ψ ⊢ k := C ∈ B
    → Ψ ⊢ k := C ∈ A `→ B
  ^:=-∀ :
      Ψ ,∙ ⊢ #S k := C ∈ A
    → Ψ ⊢ k := ↓ty0 C ∈ `∀ A

ex-will-be-solved :
    Ψ ⊢ A ≤ Σ ⊣ Ψ' ↪ B
  → Ψ ⊢ k ^∈ A
  → k := A ∈ Ψ'
ex-will-be-solved (s-empty p) inA = {!!}
ex-will-be-solved s-var inA = {!!}
ex-will-be-solved (s-ex-l^ clo x-in inst) inA = {!!}
ex-will-be-solved (s-ex-l= clo x-in s) inA = {!!}
ex-will-be-solved (s-ex-r^ clo x-in inst) inA = {!!}
ex-will-be-solved (s-ex-r= clo x-in s) inA = {!!}
ex-will-be-solved (s-arr s s₁) inA = {!!}
ex-will-be-solved (s-term-c cloA ⊢e s) inA = {!!}
ex-will-be-solved (s-term-o opnA ⊢e s s₁) inA = {!!}
ex-will-be-solved (s-∀ s) inA = {!!}
ex-will-be-solved (s-∀l s st₁ st₂) inA = {!!}
  



