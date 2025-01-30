module Implicit.Language.EnvOps.Apply where

open import Implicit.Language.Base
open import Implicit.Language.Shift
open import Implicit.Language.Lookup
open import Implicit.Language.EnvOps.Base

-- apply a env Γ to a (closed) type A, and obtain a type with no freevars.

infix 3 _≫ˣ_⇘_
infix 3 _≫_⇘_

data _≫ˣ_⇘_ : Env n m → Fin m → Type m → Set
data _≫_⇘_ : Env n m → Type m → Type m → Set

data _≫ˣ_⇘_ where
  Z∙ : Γ ,∙ ≫ˣ #0 ⇘ ‶ #0
  Z= : Γ ≫ A ⇘ A%
     → ↑ty0 A% ⇘ A%'
     → Γ ,= A ≫ˣ #0 ⇘ A%'
  S, : Γ ≫ˣ #S k ⇘ A%
     → Γ , T ≫ˣ #S k ⇘ A%
  S∙ : Γ ≫ˣ k ⇘ A%
     → ↑ty0 A% ⇘ A%'
     → Γ ,∙ ≫ˣ #S k ⇘ A%'
  S^ : Γ ≫ˣ k ⇘ A%
     → ↑ty0 A% ⇘ A%'
     → Γ ,^ ≫ˣ #S k ⇘ A%'
  S= : Γ ≫ˣ k ⇘ A%
     → ↑ty0 A% ⇘ A%'
     → Γ ,= T ≫ˣ #S k ⇘ A%'

data _≫_⇘_ where
  ap-int : Γ ≫ Int ⇘ Int
  ap-var : Γ ≫ˣ X ⇘ A
          → Γ ≫ (‶ X) ⇘ A
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

_ : (∅ ,= Int ,^ ,= Int) ≫ (‶ #0 `→ ‶ #2) ⇘ Int `→ Int
_ = ap-arr (ap-var (Z= ap-int ↑ty-int))
            (ap-var (S= (S^ (Z= ap-int ↑ty-int) ↑ty-int) ↑ty-int))

infix 3 _≫ᵍ_
data _≫ᵍ_ : Env n m → Env n m → Set where
  ap-Z : ∅ ≫ᵍ ∅
  ap-S, : Γ ≫ᵍ Γ%
        → Γ ≫ A ⇘ A%
        → Γ , A ≫ᵍ Γ% , A%
  ap-S∙ : Γ ≫ᵍ Γ%
        → Γ ,∙ ≫ᵍ Γ% ,∙
  ap-S^ : Γ ≫ᵍ Γ%
        → Γ ,^ ≫ᵍ Γ% ,^
  ap-S= : Γ ≫ᵍ Γ%
        → Γ ≫ A ⇘ A%
        → Γ ,= A ≫ᵍ Γ% ,= A%
