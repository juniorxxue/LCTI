module Implicit.Language.Shift.Base where

open import Implicit.Language.Base

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
  ↑tm-⓪ :
      e ↑tm k ⇘ e'
    → (e ⓪ A) ↑tm k ⇘ (e' ⓪ A)

infix 3 ↑tm0_⇘_
↑tm0_⇘_ : Term n m → Term (1 + n) m → Set
↑tm0_⇘_ e = _↑tm_⇘_ e #0

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
    → (up : A ↑ty k ⇘ A')
    → (e ⦂ A) ↑tyᵉ k ⇘ e' ⦂ A'
  ↑tyᵉ-Λ :
      e ↑tyᵉ #S k ⇘ e'
    → (Λ e) ↑tyᵉ k ⇘ Λ e'
  ↑tyᵉ-⓪ :
      e ↑tyᵉ k ⇘ e'
    → (upA : A ↑ty k ⇘ A')
    → (e ⓪ A) ↑tyᵉ k ⇘ (e' ⓪ A')

infix 3 ↑tyᵉ0_⇘_
↑tyᵉ0_⇘_ : Term n m → Term n (1 + m) → Set
↑tyᵉ0_⇘_ e = _↑tyᵉ_⇘_ e #0

----------------------------------------------------------------------
--+                            Shifted                             +--
----------------------------------------------------------------------

-- two-fold definition
-- 1. a type is shifted by k
-- 2. a neg definition of occurence
infix 3 _¬ε_
data _¬ε_ : Fin m → Type m → Set where
  ¬ε-int :
      k ¬ε Int
  ¬ε-var :
      k' ≢ k
    → k ¬ε (‶ k')
  ¬ε-arr :
      k ¬ε A
    → k ¬ε B
    → k ¬ε A `→ B
  ¬ε-∀ :
      #S k ¬ε A
    → k ¬ε `∀ A

-- looks like a wrong version, we need a level l to distinguish freevars and bound vars
infix 3 _¬ε⋆_
data _¬ε⋆_ : Fin m → Type m → Set where
  ¬ε⋆-int :
      k ¬ε⋆ Int
  ¬ε⋆-var :
      k #< k'
    → k ¬ε⋆ (‶ k')
  ¬ε⋆-arr :
      k ¬ε⋆ A
    → k ¬ε⋆ B
    → k ¬ε⋆ A `→ B
  ¬ε⋆-∀ :
      #S k ¬ε⋆ A
    → k ¬ε⋆ `∀ A

infix 3 _↑ty0ₙ_⇘_
data _↑ty0ₙ_⇘_ : Type m → (k : ℕ) → Type (k + m) → Set where
  ↑ty0ₙ-0 : ↑ty0 A ⇘ A'
          → A ↑ty0ₙ 1 ⇘ A'
  ↑ty0ₙ-S : A ↑ty0ₙ n ⇘ B
          → ↑ty0 B ⇘ B'
          → A ↑ty0ₙ (suc n) ⇘ B'
