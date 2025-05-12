module Implicit.Algo.Constructs.Syntax where

open import Implicit.Language.All

infixr 7 [_]↝_

data Context : ℕ → ℕ → Set where
  □     : Context n m
  τ_    : (A : Type m) → Context n m
  [_]↝_ : (e : Term n m) → Context n m → Context n m
  _⓪↝_  : (A : Type m) → Context n m → Context n m
  _◐↝_  : (A : Type m) → Context n m → Context n m -- partial type

variable
  Σ Σ' Σ* Σ'* Σ₁ Σ₂ Σ₁' Σ₂' Σ'' : Context n m
  δ δ' : Context n m

data NonEmpty : Context n m → Set where
  ne-τ    : NonEmpty (Context n m ∋⦂ τ A)
  ne-app  : NonEmpty ([ e ]↝ Σ)
  ne-tapp : NonEmpty (A ⓪↝ Σ)
  ne-par : NonEmpty (A ◐↝ Σ)

infix 3 _≊_
data _≊_ : Context n m → Context n m → Set where
  ≊Z : (Context n m ∋⦂ □) ≊ τ A
  ≊S : Σ ≊ Σ'
     → [ e ]↝ Σ ≊ [ e ]↝ Σ'
  ≊P : Σ ≊ Σ'
     → A ◐↝ Σ ≊ A ◐↝ Σ'
  ≊⓪ : Σ ≊ Σ'
     → A ⓪↝ Σ ≊ A ⓪↝ Σ'


-- assumption: A is open
infix 3 _⊢_↦_
data _⊢_↦_ : Env n m → Type m → Context n m → Set where
  tf-tvar :
    Γ ⊢ ‶ X ↦ □
  tf-∀ :
    Γ ⊢ `∀ A ↦ □
  tf-arr :
      Γ ⊢c A
    → Γ ≫ A ⇘ A%
    → Γ ⊢ B ↦ Σ
    → Γ ⊢ A `→ B ↦ A% ◐↝ Σ
