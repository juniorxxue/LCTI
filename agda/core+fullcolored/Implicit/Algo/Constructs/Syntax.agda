module Implicit.Algo.Constructs.Syntax where

open import Implicit.Language.All

-- a list of types
data ParType : ℕ → Set where
  □ : ParType m
  _◐↝_ : (A : Type m) → ParType m → ParType m

variable
  P P₁ P₂ P' : ParType m

data EContext : ℕ → Set where
  τ_  : (A : Type m) → EContext m
  p_  : (P : ParType m) → EContext m

infixr 7 [_]↝_

data Context : ℕ → ℕ → Set where
  𝔼     : EContext m → Context n m
  [_]↝_ : (e : Term n m) → Context n m → Context n m
  _⓪↝_  : (A : Type m) → Context n m → Context n m

variable
  Σ Σ' Σ* Σ'* Σ₁ Σ₂ Σ₁' Σ₂' Σ'' : Context n m
  δ δ' δ₁ δ₂ : EContext m

data NonEmpty : Context n m → Set where
  -- ?
  ne-app  : NonEmpty ([ e ]↝ Σ)
  ne-tapp : NonEmpty (A ⓪↝ Σ)


infix 3 _≊P_
data _≊P_ : ParType m → ParType m → Set where
  ≊P-Z : □ ≊P P
  ≊P-S : P₁ ≊P P₂
       → A ◐↝ P₁ ≊P A ◐↝ P₂

infix 3 _≊E_
data _≊E_ : EContext m → EContext m → Set where
  p2τ : p P ≊E τ A
  p2p : P₁ ≊P P₂
      → p P₁ ≊E p P₂

infix 3 _≊_
data _≊_ : Context n m → Context n m → Set where
  ≋E : δ₁ ≊E δ₂
     → (Context n m ∋⦂ 𝔼 δ₁) ≊ 𝔼 δ₂
  ≊S : Σ ≊ Σ'
     → [ e ]↝ Σ ≊ [ e ]↝ Σ'
  ≊⓪ : Σ ≊ Σ'
     → A ⓪↝ Σ ≊ A ⓪↝ Σ'

-- assumption: A is open
infix 3 _⊢_↦₁_
data _⊢_↦₁_ : Env n m → Type m → ParType m → Set where
  tf-tvar :
    Γ ⊢ ‶ X ↦₁ □
  tf-∀ :
    Γ ⊢ `∀ A ↦₁ □
  tf-arr :
      Γ ⊢c A
    → Γ ≫ A ⇘ A%
    → Γ ⊢ B ↦₁ P
    → Γ ⊢ A `→ B ↦₁ A% ◐↝ P


-- sugar
`□ : Context n m
`□ = 𝔼 (p □)

`τ : Type m → Context n m
`τ A = 𝔼 (τ A)

`p : ParType m → Context n m
`p P = 𝔼 (p P)

_`◐↝_ : Type m → ParType m → Context n m
A `◐↝ P = 𝔼 (p (A ◐↝ P))
