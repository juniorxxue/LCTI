module Implicit.Language.Ground.Base where

open import Implicit.Language.Base
open import Implicit.Language.Shift.Base
open import Implicit.Language.Lookup.Base
open import Implicit.Language.EnvOps.Base

-- this only works on the subtyping environment
infix 3 _≫_⇘_
data _≫_⇘_ : Env n m → Type m → Type m → Set
data _≫_⇘_ where
  grd-int : Δ ≫ Int ⇘ Int
  grd-var= : Δ ∋ X := A
           → Δ ≫ (‶ X) ⇘ A
  grd-var∙ : Δ ∋∙ X
          → Δ ≫ (‶ X) ⇘ (‶ X)
  grd-arr : Δ ≫ A ⇘ A%
          → Δ ≫ B ⇘ B%
          → Δ ≫ (A `→ B) ⇘ A% `→ B%
  grd-∀   : Δ ,∙ ≫ A ⇘ A%
          → Δ ≫ `∀ A ⇘ `∀ A%
