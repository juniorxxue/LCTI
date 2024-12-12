module Implicit.Algo.Syntax where

open import Implicit.Language

infixl 4 _,^

-- Env for algorithmic subtyping
data SEnv : ℕ → ℕ → Set where
  ∅     : SEnv 0 0
  _,_   : SEnv n m → (A : Type m) → SEnv (1 + n) m
  _,∙   : SEnv n m → SEnv n (1 + m) -- universal variable
  _,^   : SEnv n m → SEnv n (1 + m) -- existential variable
  _,=_  : SEnv n m → (A : Type m) → SEnv n (1 + m) -- solved equation

infixr 7 [_]↝_

data Context : ℕ → ℕ → Set where
  □     : Context n m
  τ_    : (A : Type m) → Context n m
  [_]↝_ : (e : Term n m) → Context n m → Context n m

data NonEmpty : Context n m → Set where
  ne-τ    : ∀ {A : Type m} → NonEmpty (Context n m ∋⦂ τ A)
  ne-app  : ∀ {e} {Σ : Context n m} → NonEmpty ([ e ]↝ Σ)

data GenericConsumer : Term n m → Set where
  gc-i : ∀ {i} → GenericConsumer (Term n m ∋⦂ lit i)
  gc-var : ∀ {x} → GenericConsumer (Term n m ∋⦂ ` x)
  gc-ann : ∀ {e : Term n m} {A} → GenericConsumer (e ⦂ A)
  gc-tlam : ∀ {e : Term n (1 + m)} → GenericConsumer (Λ e)


data Polar : Set where
  ≤⁺ ≤⁻ : Polar

⋆ : Polar → Polar
⋆ ≤⁺ = ≤⁻
⋆ ≤⁻ = ≤⁺
