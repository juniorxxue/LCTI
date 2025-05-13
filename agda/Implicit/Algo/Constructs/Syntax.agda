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
infix 3 _⊢_↦₁_
data _⊢_↦₁_ : Env n m → Type m → Context n m → Set where
  tf-tvar :
    Γ ⊢ ‶ X ↦₁ □
  tf-∀ :
    Γ ⊢ `∀ A ↦₁ □
  tf-arr :
      Γ ⊢c A
    → Γ ≫ A ⇘ A%
    → Γ ⊢ B ↦₁ Σ
    → Γ ⊢ A `→ B ↦₁ A% ◐↝ Σ

infix 3 _↦₂_
data _↦₂_ : Type m → Context n m → Set where
  tf-int : Int ↦₂ (Context n m ∋⦂ τ Int)
  tf-tvar : ‶ X ↦₂ (Context n m ∋⦂ τ (‶ X))
  tf-∀ : `∀ A ↦₂ (Context n m ∋⦂ τ (`∀ A))
  tf-arr : B ↦₂ Σ
         → A `→ B ↦₂ A ◐↝ Σ

infix 3 _⟼_
data _⟼_ : Context n m → Context n m → Set where
  tf-empty : □ ⟼ (Context n m ∋⦂ □)
  tf-τ : A ↦₂ δ
       → τ A ⟼ δ
  tf-term : Σ ⟼ δ
         → [ e ]↝ Σ ⟼ [ e ]↝ δ
  tf-tapp : Σ ⟼ δ
          → A ⓪↝ Σ ⟼ A ⓪↝ δ
  tf-par : Σ ⟼ δ
          → A ◐↝ Σ ⟼ A ◐↝ δ


-- to restrict the rule in algo, letting it to be syntax-directed

data 𝔽 : Context n m → Set where
  𝔽-term : 𝔽 ([ e ]↝ Σ)
  𝔽-par  : 𝔽 (A ◐↝ Σ)
