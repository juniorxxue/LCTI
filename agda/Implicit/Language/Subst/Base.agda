module Implicit.Language.Subst.Base where

open import Implicit.Language.Base
open import Implicit.Language.Shift

private variable
  A A' B B' C C' D : Type m
  e e' e₁ e₁' e₂ e₂' : Term n m
  k X : Fin m
  i : ℕ
  x : Fin n
  


----------------------------------------------------------------------
--+                         Function Ver.                          +--
----------------------------------------------------------------------

-- type subst
infix 6 ⟦_/_⟧_
⟦_/_⟧_ : Fin (1 + m) → Type m → Type (1 + m) → Type m
⟦ k / A ⟧ Int      = Int
⟦ k / A ⟧ (‶ X) with k #≟ X
... | yes p = A
... | no ¬p = ‶ punchOut {i = k} {j = X} ¬p
⟦ k / A ⟧ (B `→ C) = (⟦ k / A ⟧ B) `→ (⟦ k / A ⟧ C)
⟦ k / A ⟧ (`∀ B)   = `∀ (⟦ #S k / ↑ty0 A ⟧ B)

infix 7 ⟦_⟧_
⟦_⟧_ : Type m → Type (1 + m) → Type m
⟦_⟧_ = ⟦_/_⟧_ #0

-- type subst in term
infix 6 ⟦_/_⟧ᵉ_
⟦_/_⟧ᵉ_ : Fin (1 + m) → Type m → Term n (1 + m) → Term n m
⟦ k / A ⟧ᵉ lit i = lit i
⟦ k / A ⟧ᵉ ` x = ` x
⟦ k / A ⟧ᵉ (ƛ e) = ƛ (⟦ k / A ⟧ᵉ e)
⟦ k / A ⟧ᵉ e₁ · e₂ = (⟦ k / A ⟧ᵉ e₁) · (⟦ k / A ⟧ᵉ e₂)
⟦ k / A ⟧ᵉ (e ⦂ B) = (⟦ k / A ⟧ᵉ e) ⦂ (⟦ k / A ⟧ B)
⟦ k / A ⟧ᵉ (Λ e) = Λ ⟦ #S k / ↑ty0 A ⟧ᵉ e

infix 7 ⟦_⟧ᵉ_
⟦_⟧ᵉ_ : Type m → Term n (1 + m) → Term n m
⟦_⟧ᵉ_ = ⟦_/_⟧ᵉ_ #0

-- unshift is just substing with a random type, be careful to use it
↓ty0 : Type (1 + m) → Type m
↓ty0 A = ⟦ Int ⟧ A

----------------------------------------------------------------------
--+                         Relation Ver.                          +--
----------------------------------------------------------------------

infix 3 ⟦_/_⟧ˣ
⟦_/_⟧ˣ : Fin (1 + m) → Type m → Fin (1 + m) → Type m
⟦ k / A ⟧ˣ X with k #≟ X
... | yes p = A
... | no ¬p = ‶ punchOut {i = k} {j = X} ¬p

-- type subst
infix 3 ⟦_/_⟧_⇘_
data ⟦_/_⟧_⇘_ : Fin (1 + m) → Type m → Type (1 + m) → Type m → Set where
  st-int :
      ⟦ k / A ⟧ Int ⇘ Int
  st-var :
      ⟦ k / A ⟧ (‶ X) ⇘ ⟦ k / A ⟧ˣ X
  st-arr :
      ⟦ k / A ⟧ B ⇘ B'
    → ⟦ k / A ⟧ C ⇘ C'
    → ⟦ k / A ⟧ (B `→ C) ⇘ B' `→ C'
  st-∀ :
      (up : ↑ty0 A ⇘ A')
    → ⟦ #S k / A' ⟧ B ⇘ B'
    → ⟦ k / A ⟧ (`∀ B) ⇘ `∀ B'

⟦_⟧_⇘_ : Type m → Type (1 + m) → Type m → Set
⟦_⟧_⇘_ = ⟦_/_⟧_⇘_ #0

-- type subst in term
infix 5 ⟦_/_⟧ᵉ_⇘_
data ⟦_/_⟧ᵉ_⇘_ : Fin (1 + m) → Type m → Term n (1 + m) → Term n m → Set where
  st-lit :
      ⟦ k / A ⟧ᵉ lit i ⇘ (Term n m ∋⦂ lit i)
  st-var :
      ⟦ k / A ⟧ᵉ ` x ⇘ (Term n m ∋⦂ ` x)
  st-ƛ : ∀ {k A e e'}
    → ⟦ k / A ⟧ᵉ e ⇘ e'
    → ⟦ k / A ⟧ᵉ (ƛ e) ⇘ (Term n m ∋⦂ ƛ e')
  st-· :
      ⟦ k / A ⟧ᵉ e₁ ⇘ e₁'
    → ⟦ k / A ⟧ᵉ e₂ ⇘ e₂'
    → ⟦ k / A ⟧ᵉ (e₁ · e₂) ⇘ (Term n m ∋⦂ e₁' · e₂')
  st-⦂ :
      ⟦ k / A ⟧ᵉ e ⇘ e'
    → ⟦ k / A ⟧ B ⇘ B'
    → ⟦ k / A ⟧ᵉ (e ⦂ B) ⇘ (Term n m ∋⦂ e' ⦂ B')
  st-Λ :
      ⟦ #S k / ↑ty0 A ⟧ᵉ e ⇘ e'
    → ⟦ k / A ⟧ᵉ (Λ e) ⇘ (Term n m ∋⦂ Λ e')
