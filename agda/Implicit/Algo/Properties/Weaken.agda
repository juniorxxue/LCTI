module Implicit.Algo.Properties.Weaken where

open import Implicit.Language
open import Implicit.Algo.Base

postulate
  s-weaken,0 : Γ ⊢ A ⌞ ≤ ⌝ Σ ⊣ Δ ↪ B
             → ↑tmᶜ0 Σ ⇘ Σ'
             → Γ , T ⊢ A ⌞ ≤ ⌝ Σ' ⊣ Δ , T ↪ B
