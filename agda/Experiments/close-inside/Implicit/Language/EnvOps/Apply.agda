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
  app-int : Γ ≫ Int ⇘ Int
  app-var : Γ ≫ˣ X ⇘ A
          → Γ ≫ (‶ X) ⇘ A
  app-arr : Γ ≫ A ⇘ A%
          → Γ ≫ B ⇘ B%
          → Γ ≫ (A `→ B) ⇘ A% `→ B%
  app-∀   : Γ ,∙ ≫ A ⇘ A%
          → Γ ≫ `∀ A ⇘ `∀ A%

_ : (∅ ,= Int ,^ ,= Int) ≫ (‶ #0 `→ ‶ #2) ⇘ Int `→ Int
_ = app-arr (app-var (Z= app-int ↑ty-int))
            (app-var (S= (S^ (Z= app-int ↑ty-int) ↑ty-int) ↑ty-int))
