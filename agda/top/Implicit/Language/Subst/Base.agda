module Implicit.Language.Subst.Base where

open import Implicit.Language.Base
open import Implicit.Language.Shift.All

private variable
  i : ℕ


----------------------------------------------------------------------
--+                         Relation Ver.                          +--
----------------------------------------------------------------------

infix 3 ⟦_/_⟧ˣ_⇘_
data ⟦_/_⟧ˣ_⇘_ : Fin (1 + m) → Type m → Fin (1 + m) → Type m → Set where
  stx-eq  : ⟦ k / A ⟧ˣ k ⇘ A
  stx-neq : (¬p : k ≢ X)
          → ⟦ k / A ⟧ˣ X ⇘ ‶ punchOut {i = k} {j = X} ¬p


stx-neq-helper : (¬p : k ≢ X)
               → Y ≡ punchOut {i = k} {j = X} ¬p
               → ⟦ k / A ⟧ˣ X ⇘ ‶ Y
stx-neq-helper ¬p refl = stx-neq ¬p

-- type subst
infix 3 ⟦_/_⟧_⇘_
data ⟦_/_⟧_⇘_ : Fin (1 + m) → Type m → Type (1 + m) → Type m → Set where
  st-int :
      ⟦ k / A ⟧ Int ⇘ Int
  st-top :
      ⟦ k / A ⟧ Top ⇘ Top
  st-var :
      (stx : ⟦ k / A ⟧ˣ X ⇘ B)
    → ⟦ k / A ⟧ (‶ X) ⇘ B
  st-arr :
      ⟦ k / A ⟧ B ⇘ B*
    → ⟦ k / A ⟧ C ⇘ C*
    → ⟦ k / A ⟧ (B `→ C) ⇘ B* `→ C*
  st-∀ :
      (up : ↑ty0 A ⇘ A')
    → ⟦ #S k / A' ⟧ B ⇘ B'
    → ⟦ k / A ⟧ (`∀ B) ⇘ `∀ B'

infix 3 ⟦_⟧_⇘_
⟦_⟧_⇘_ : Type m → Type (1 + m) → Type m → Set
⟦_⟧_⇘_ = ⟦_/_⟧_⇘_ #0

-- type subst in term
infix 3 ⟦_/_⟧ᵉ_⇘_
data ⟦_/_⟧ᵉ_⇘_ : Fin (1 + m) → Type m → Term n (1 + m) → Term n m → Set where
  st-lit :
      ⟦ k / A ⟧ᵉ lit i ⇘ (Term n m ∋⦂ lit i)
  st-var :
      ⟦ k / A ⟧ᵉ ` x ⇘ (Term n m ∋⦂ ` x)
  st-ƛ :
      ⟦ k / A ⟧ᵉ e ⇘ e'
    → ⟦ k / A ⟧ᵉ (ƛ e) ⇘ (Term n m ∋⦂ ƛ e')
  st-· :
      ⟦ k / A ⟧ᵉ e₁ ⇘ e₁'
    → ⟦ k / A ⟧ᵉ e₂ ⇘ e₂'
    → ⟦ k / A ⟧ᵉ (e₁ · e₂) ⇘ (Term n m ∋⦂ e₁' · e₂')
  st-⦂ :
      ⟦ k / A ⟧ᵉ e ⇘ e'
    → (st : ⟦ k / A ⟧ B ⇘ B')
    → ⟦ k / A ⟧ᵉ (e ⦂ B) ⇘ (Term n m ∋⦂ e' ⦂ B')
  st-Λ :
      ⟦ #S k / A' ⟧ᵉ e ⇘ e'
    → (up : ↑ty0 A ⇘ A')
    → ⟦ k / A ⟧ᵉ (Λ e) ⇘ (Term n m ∋⦂ Λ e')
  st-⓪ :
      ⟦ k / A ⟧ᵉ e ⇘ e'
    → (st : ⟦ k / A ⟧ B ⇘ B')
    → ⟦ k / A ⟧ᵉ (e ⓪ B) ⇘ (Term n m ∋⦂ e' ⓪ B')


infix 3 ⟦_⟧ᵉ_⇘_
⟦_⟧ᵉ_⇘_ : Type m → Term n (1 + m) → Term n m → Set
⟦_⟧ᵉ_⇘_ = ⟦_/_⟧ᵉ_⇘_ #0
