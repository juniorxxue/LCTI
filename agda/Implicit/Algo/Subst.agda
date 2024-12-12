module Implicit.Algo.Subst where

open import Implicit.Language
open import Implicit.Algo.Syntax

private variable
  k : Fin m
  A A' B B' C D : Type m
  Σ Σ' : Context n m
  e e' : Term n m
  Γ Γ' : Env n m

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
data [_/_]_⟹_ : Type m → Fin m → Env n m → Env n m → Set where
  ⟹^0 : (up : ↑ty0 A ⇘ A')
      → [ A' / #0 ] (Γ ,^) ⟹ (Γ ,= A)

  ⟹^S : [ A / k ] Γ ⟹ Γ'
      → (up : ↑ty0 A ⇘ A')
      → [ A' / #S k ] (Γ ,^) ⟹ Γ' ,^

  ⟹∙S : [ A / k ] Γ ⟹ Γ'
      → (up : ↑ty0 A ⇘ A')
      → [ A' / #S k ] (Γ ,∙) ⟹ (Γ' ,∙)

  ⟹,S : [ A / k ] Γ ⟹ Γ'
      → [ A / k ] (Γ , B) ⟹ (Γ' , B)

  ⟹=S : (up : ⟦ B ⟧ A ⇘ A')
      → [ A' / k ] Γ ⟹ Γ'
      → [ A / #S k ] (Γ ,= B) ⟹ (Γ' ,= B)
