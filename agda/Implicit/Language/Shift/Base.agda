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
private variable
  k X : Fin m
  x y : Fin n
  A B A' B' : Type m
  e e' e₁ e₂ e₁' e₂' : Term n m

infix 3 _↑tm_⇘_
data _↑tm_⇘_ : Term n m → Fin (1 + n) → Term (1 + n) m → Set where
  ↑tm-lit : ∀ {num : ℕ}
    → (Term n m ∋⦂ lit num) ↑tm x ⇘ lit num
  ↑tm-var :
      (Term n m ∋⦂ (` x)) ↑tm y ⇘ ` (punchIn y x)
  ↑tm-ƛ :
      e ↑tm #S k ⇘ e'
    → (ƛ e) ↑tm k ⇘ ƛ e'
  ↑tm-app :
      e₁ ↑tm k ⇘ e₁'
    → e₂ ↑tm k ⇘ e₂'
    → (e₁ · e₂) ↑tm k ⇘ e₁' · e₂'
  ↑tm-⦂ :
      e ↑tm k ⇘ e'
    → (e ⦂ A) ↑tm k ⇘ e' ⦂ A
  ↑tm-Λ :
      e ↑tm k ⇘ e'
    → (Λ e) ↑tm k ⇘ Λ e'

infix 3 _↑ty_⇘_
data _↑ty_⇘_ : Type m → Fin (1 + m) → Type (1 + m) → Set where
  ↑ty-int :
      Int ↑ty k ⇘ Int
  ↑ty-var :
      (‶ X) ↑ty k ⇘ ‶ punchIn k X
  ↑ty-arr :
      A ↑ty k ⇘ A'
    → B ↑ty k ⇘ B'
    → A `→ B ↑ty k ⇘ A' `→ B'
  ↑ty-∀ :
      A ↑ty #S k ⇘ A'
    → (`∀ A) ↑ty k ⇘ `∀ A'

infix 3 ↑ty0_⇘_
↑ty0_⇘_ : Type m → Type (1 + m) → Set
↑ty0_⇘_ A = _↑ty_⇘_ A #0

infix 3 _↑tyᵉ_⇘_
data _↑tyᵉ_⇘_ : Term n m → Fin (1 + m) → Term n (1 + m) → Set where
  ↑tyᵉ-lit : ∀ {num : ℕ}
    → (Term n m ∋⦂ lit num) ↑tyᵉ k ⇘ lit num
  ↑tyᵉ-var :
      (` x) ↑tyᵉ k ⇘ ` x
  ↑tyᵉ-ƛ :
      e ↑tyᵉ k ⇘ e'
    → (ƛ e) ↑tyᵉ k ⇘ ƛ e'
  ↑tyᵉ-app :
      e₁ ↑tyᵉ k ⇘ e₁'
    → e₂ ↑tyᵉ k ⇘ e₂'
    → (e₁ · e₂) ↑tyᵉ k ⇘ e₁' · e₂'
  ↑tyᵉ-⦂ :
      e ↑tyᵉ k ⇘ e'
    → A ↑ty k ⇘ A'
    → (e ⦂ A) ↑tyᵉ k ⇘ e' ⦂ A'
  ↑tyᵉ-Λ :
      e ↑tyᵉ #S k ⇘ e'
    → (Λ e) ↑tyᵉ k ⇘ Λ e'

infix 3 ↑tyᵉ0_⇘_
↑tyᵉ0_⇘_ : Term n m → Term n (1 + m) → Set
↑tyᵉ0_⇘_ e = _↑tyᵉ_⇘_ e #0

----------------------------------------------------------------------
--+                            Shifted                             +--
----------------------------------------------------------------------

data Shifted : Type m → Fin m → Set where
  sfd-int : ∀ {b} → Shifted (Type m ∋⦂ Int) b
  sfd-var : ∀ {k : Fin m} {b} → k ≢ b → Shifted (‶ k) b
  sfd-arr : ∀ {A B : Type m} {b} → Shifted A b → Shifted B b → Shifted (A `→ B) b
  sfd-∀ : ∀ {A : Type (1 + m)} {b} → Shifted A (#S b) → Shifted (`∀ A) b

