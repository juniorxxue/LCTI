module Implicit.Algo.Constructs.Syntax where

open import Implicit.Language.All

infixr 7 [_]↝_

data Context : ℕ → ℕ → Set where
  □     : Context n m
  τ_    : (A : Type m) → Context n m
  [_]↝_ : (e : Term n m) → Context n m → Context n m

variable
  Σ Σ' Σ* Σ'* Σ₁ Σ₂ Σ₁' Σ₂' Σ'' : Context n m

data NonEmpty : Context n m → Set where
  ne-τ    : ∀ {A : Type m} → NonEmpty (Context n m ∋⦂ τ A)
  ne-app  : ∀ {e} {Σ : Context n m} → NonEmpty ([ e ]↝ Σ)
