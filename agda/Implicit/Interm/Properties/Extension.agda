module Implicit.Interm.Properties.Extension where

open import Implicit.Language.All
open import Implicit.Interm.Base

postulate
  s-⊆-prv : Γ ⊢ j # A ⌞ ≤ ⌝ B
          → Γ ⊆ Δ
          → Δ ⊢ j # A ⌞ ≤ ⌝ B


  t-⊆-prv : 𝕣 Γ ⊢ j # e ⦂ A
          → Γ ⊆ Δ
          → 𝕣 Δ ⊢ j # e ⦂ A
