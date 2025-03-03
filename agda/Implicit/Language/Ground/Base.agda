module Implicit.Language.Ground.Base where

open import Implicit.Language.Base
open import Implicit.Language.Shift.Base
open import Implicit.Language.Lookup.Base
open import Implicit.Language.EnvOps.Base

-- apply a env Γ to a (closed) type A, and obtain a ground type (with no freevars).
infix 3 _≫_⇘_

data _≫_⇘_ : Env n m → Type m → Type m → Set
data _≫_⇘_ where
  grd-int : Γ ≫ Int ⇘ Int
  grd-var= : Γ ∋ X := A
          → Γ ≫ (‶ X) ⇘ A
  grd-var∙ : Γ ∋∙ X
          → Γ ≫ (‶ X) ⇘ (‶ X)
  grd-arr : Γ ≫ A ⇘ A%
          → Γ ≫ B ⇘ B%
          → Γ ≫ (A `→ B) ⇘ A% `→ B%
  grd-∀   : Γ ,∙ ≫ A ⇘ A%
          → Γ ≫ `∀ A ⇘ `∀ A%

infix 3 _≫²_⇘_

data _≫²_⇘_ : Env n m → Type m → Type m → Set
data _≫²_⇘_ where
  grd-int : Γ ≫² Int ⇘ Int
  grd-var=¹ : Γ ∋ X :=¹ A
          → Γ ≫² (‶ X) ⇘ (‶ X)
  grd-var=² : Γ ∋ X :=² A
          → Γ ≫² (‶ X) ⇘ A
  grd-var∙ : Γ ∋∙ X
          → Γ ≫² (‶ X) ⇘ (‶ X)
  grd-arr : Γ ≫² A ⇘ A%
          → Γ ≫² B ⇘ B%
          → Γ ≫² (A `→ B) ⇘ A% `→ B%
  grd-∀   : Γ ,∙ ≫² A ⇘ A%
          → Γ ≫² `∀ A ⇘ `∀ A%

infix 3 _≫ᵉ_⇘_
data _≫ᵉ_⇘_ : Env n m → Term n m → Term n m → Set where
  grd-lit : ∀ {num} → Γ ≫ᵉ lit num ⇘ lit num
  grd-var : Γ ≫ᵉ (` x) ⇘ (` x)
  grd-lam : Γ , A ≫ᵉ e ⇘ e%
         → Γ ≫ᵉ (ƛ e) ⇘ ƛ e%
  grd-ann : (apA : Γ ≫ A ⇘ A%)
          → Γ ≫ᵉ e ⇘ e%
          → Γ ≫ᵉ (e ⦂ A) ⇘ (e% ⦂ A%)
  grd-app : Γ ≫ᵉ e₁ ⇘ e₁%
         → Γ ≫ᵉ e₂ ⇘ e₂%
         → Γ ≫ᵉ (e₁ · e₂) ⇘ e₁% · e₂%
  grd-tlam : Γ ,∙ ≫ᵉ e ⇘ e%
         → Γ ≫ᵉ (Λ e) ⇘ Λ e%

infix 3 _≫ᵍ_
data _≫ᵍ_ : Env n m → Env n m → Set where
  grd-Z : ∅ ≫ᵍ ∅
  grd-S, : Γ ≫ᵍ Γ%
        → (apA : Γ% ≫ A ⇘ A%)
        → Γ , A ≫ᵍ Γ% , A%
  grd-S∙ : Γ ≫ᵍ Γ%
        → Γ ,∙ ≫ᵍ Γ% ,∙
  grd-S^ : Γ ≫ᵍ Γ%
        → Γ ,^ ≫ᵍ Γ% ,^
  grd-S= : Γ ≫ᵍ Γ%
        → Γ% ≫ A ⇘ A%
        → Γ ,= A ≫ᵍ Γ% ,= A%
