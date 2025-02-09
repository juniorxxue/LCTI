module Implicit.Algo.Subst where

open import Implicit.Language.All
open import Implicit.Algo.Syntax

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
