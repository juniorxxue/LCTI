module Implicit.Language.EnvOps.Apply where

open import Implicit.Language.Base
open import Implicit.Language.Shift
open import Implicit.Language.Lookup
open import Implicit.Language.EnvOps.Base

-- apply a env Γ to a type A, and obtain a type with no freevars.

infix 3 _≫ˣ_⇘_
data _≫ˣ_⇘_ : Env n m → Fin m → Type m → Set where

infix 3 _≫_⇘_
data _≫_⇘_ : Env n m → Type m → Type m → Set where
  app-int : Γ ≫ Int ⇘ Int
  app-var : Γ ≫ˣ X ⇘ A
          → Γ ≫ (‶ X) ⇘ A
  app-arr : Γ ≫ A ⇘ A%
          → Γ ≫ B ⇘ B%
          → Γ ≫ (A `→ B) ⇘ A% `→ B%
  app-∀   : Γ ,∙ ≫ A ⇘ A%
          → Γ ≫ `∀ A ⇘ `∀ A%
