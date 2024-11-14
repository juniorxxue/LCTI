module Implicit.Language.Shift.Base where

open import Implicit.Language.Base

----------------------------------------------------------------------
--+                         Function Ver.                          +--
----------------------------------------------------------------------

-- type shift
↑ty : Fin (1 + m) → Type m → Type (1 + m)
↑ty k Int      = Int
↑ty k (‶ X)    = ‶ punchIn k X
↑ty k (A `→ B) = ↑ty k A `→ ↑ty k B
↑ty k (`∀ A)   = `∀ (↑ty (#S k) A)

↑ty0 : Type m → Type (1 + m)
↑ty0 = ↑ty #0

-- term shift
↑tm : Fin (1 + n) → Term n m → Term (1 + n) m
↑tm k (lit i)    = lit i
↑tm k (` x)      = ` (punchIn k x)
↑tm k (ƛ e)      = ƛ (↑tm (#S k) e)
↑tm k (e₁ · e₂)  = ↑tm k e₁ · ↑tm k e₂
↑tm k (e ⦂ A)    = (↑tm k e) ⦂ A
↑tm k (Λ e)      = Λ (↑tm k e)

↑tm0 : Term n m → Term (1 + n) m
↑tm0 = ↑tm #0

-- type shift in term
↑tyᵉ : Fin (1 + m) → Term n m → Term n (1 + m)
↑tyᵉ k (lit i)    = lit i
↑tyᵉ k (` x)      = ` x
↑tyᵉ k (ƛ e)      = ƛ (↑tyᵉ k e)
↑tyᵉ k (e₁ · e₂)  = ↑tyᵉ k e₁ · ↑tyᵉ k e₂
↑tyᵉ k (e ⦂ A)    = (↑tyᵉ k e) ⦂ (↑ty k A)
↑tyᵉ k (Λ e)      = Λ (↑tyᵉ (#S k) e)

↑tyᵉ0 : Term n m → Term n (1 + m)
↑tyᵉ0 = ↑tyᵉ #0

----------------------------------------------------------------------
--+                         Relation Ver.                          +--
----------------------------------------------------------------------

infix 3 _↑ty_⇘_

data _↑ty_⇘_ : Type m → Fin (1 + m) → Type (1 + m) → Set where
  ↑ty-int : ∀ {k : Fin (1 + m)}
    → Int ↑ty k ⇘ Int
  ↑ty-var : ∀ {k : Fin (1 + m)} {X}
    → (‶ X) ↑ty k ⇘ ‶ punchIn k X
  ↑ty-arr : ∀ {A B : Type m} {A' B' : Type (1 + m)} {k}
    → A ↑ty k ⇘ A'
    → B ↑ty k ⇘ B'
    → A `→ B ↑ty k ⇘ A' `→ B'
  ↑ty-∀ : ∀ {A : Type (1 + m)} {A' k}
    → A ↑ty #S k ⇘ A'
    → (`∀ A) ↑ty k ⇘ `∀ A'

↑ty0_⇘_ : Type m → Type (1 + m) → Set
↑ty0_⇘_ A A' = _↑ty_⇘_ A #0 A'
