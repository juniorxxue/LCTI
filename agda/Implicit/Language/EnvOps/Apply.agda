module Implicit.Language.EnvOps.Apply where

open import Implicit.Language.Base
open import Implicit.Language.Shift
open import Implicit.Language.Lookup
open import Implicit.Language.EnvOps.Base

-- apply a env Γ to a (closed) type A, and obtain a type with no freevars.
infix 3 _≫_⇘_

data _≫_⇘_ : Env n m → Type m → Type m → Set
data _≫_⇘_ where
  ap-int : Γ ≫ Int ⇘ Int
  ap-var= : Γ ∋ X := A
          → Γ ≫ (‶ X) ⇘ A
  ap-var∙ : Γ ∋∙ X
          → Γ ≫ (‶ X) ⇘ (‶ X)
  ap-arr : Γ ≫ A ⇘ A%
          → Γ ≫ B ⇘ B%
          → Γ ≫ (A `→ B) ⇘ A% `→ B%
  ap-∀   : Γ ,∙ ≫ A ⇘ A%
          → Γ ≫ `∀ A ⇘ `∀ A%

infix 3 _≫ᵉ_⇘_
data _≫ᵉ_⇘_ : Env n m → Term n m → Term n m → Set where
  ap-lit : ∀ {num} → Γ ≫ᵉ lit num ⇘ lit num
  ap-var : Γ ≫ᵉ (` x) ⇘ (` x)
  ap-lam : Γ , A ≫ᵉ e ⇘ e%
         → Γ ≫ᵉ (ƛ e) ⇘ ƛ e%
  ap-ann : (apA : Γ ≫ A ⇘ A%)
          → Γ ≫ᵉ e ⇘ e%
          → Γ ≫ᵉ (e ⦂ A) ⇘ (e% ⦂ A%)
  ap-app : Γ ≫ᵉ e₁ ⇘ e₁%
         → Γ ≫ᵉ e₂ ⇘ e₂%
         → Γ ≫ᵉ (e₁ · e₂) ⇘ e₁% · e₂%
  ap-tlam : Γ ,∙ ≫ᵉ e ⇘ e%
         → Γ ≫ᵉ (Λ e) ⇘ Λ e%

infix 3 _≫ᵍ_
data _≫ᵍ_ : Env n m → Env n m → Set where
  ap-Z : ∅ ≫ᵍ ∅
  ap-S, : Γ ≫ᵍ Γ%
        → (apA : Γ% ≫ A ⇘ A%)
        → Γ , A ≫ᵍ Γ% , A%
  ap-S∙ : Γ ≫ᵍ Γ%
        → Γ ,∙ ≫ᵍ Γ% ,∙
  ap-S^ : Γ ≫ᵍ Γ%
        → Γ ,^ ≫ᵍ Γ% ,^
  ap-S= : Γ ≫ᵍ Γ%
        → Γ% ≫ A ⇘ A%
        → Γ ,= A ≫ᵍ Γ% ,= A%
