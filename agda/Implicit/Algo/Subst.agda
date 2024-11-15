module Implicit.Algo.Subst where

open import Implicit.Language
open import Implicit.Algo.Syntax

private variable
  k : Fin m
  A B B' C D : Type m
  Σ Σ' : Context n m
  e e' : Term n m

-- subst a type in context
infix 3 ⟦_/_⟧ᶜ_⇘_
data ⟦_/_⟧ᶜ_⇘_ : Fin (1 + m) → Type m → Context n (1 + m) → Context n m → Set where
  empty :
      ⟦ k / A ⟧ᶜ □ ⇘ (Context n m ∋⦂ □)
  fulltype :
      (st : ⟦ k / A ⟧ B ⇘ B')
    → ⟦ k / A ⟧ᶜ (τ B) ⇘ (Context n m ∋⦂ (τ B'))
  term :
      ⟦ k / A ⟧ᶜ Σ ⇘ Σ'
    → (ste : ⟦ k / A ⟧ᵉ e ⇘ e')
    → ⟦ k / A ⟧ᶜ ([ e ]↝ Σ) ⇘ (Context n m ∋⦂ ([ e' ]↝ Σ'))

infix 3 ⟦_⟧ᶜ_⇘_
⟦_⟧ᶜ_⇘_ : Type m → Context n (1 + m) → Context n m → Set
⟦_⟧ᶜ_⇘_ = ⟦_/_⟧ᶜ_⇘_ #0


-- replace entry ^a with a solution ^a=A in an environment
infix 3 [_/_]_⟹_
data [_/_]_⟹_ : Type m → Fin m → SEnv n m → SEnv n m → Set where
  ⟹^0 : ∀ {Ψ : SEnv n m} {A A'}
    → ↑ty0 A ⇘ A'
    → [ A' / #0 ] (Ψ ,^) ⟹ (Ψ ,= A)

  ⟹^S : ∀ {Ψ Ψ' : SEnv n m} {A k A'}
    → [ A / k ] Ψ ⟹ Ψ'
    → ↑ty0 A ⇘ A'
    → [ A' / #S k ] (Ψ ,^) ⟹ Ψ' ,^

  ⟹∙S : ∀ {Ψ Ψ' : SEnv n m} {A k A'}
    → [ A / k ] Ψ ⟹ Ψ'
    → ↑ty0 A ⇘ A'
    → [ A' / #S k ] (Ψ ,∙) ⟹ (Ψ' ,∙)

  ⟹,S : ∀ {Ψ Ψ' : SEnv n m} {A k B}
    → [ A / k ] Ψ ⟹ Ψ'
    → [ A / k ] (Ψ , B) ⟹ (Ψ' , B)

  ⟹=S : ∀ {Ψ Ψ' : SEnv n m} {A A' B k}
    → (up : ⟦ B ⟧ A ⇘ A')
    → [ A' / k ] Ψ ⟹ Ψ'
    → [ A / #S k ] (Ψ ,= B) ⟹ (Ψ' ,= B)
