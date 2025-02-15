module Implicit.Algo.Properties.Strengthen where

open import Implicit.Language.All
open import Implicit.Algo.Base

postulate
  s-strengthen,0 : Γ , T ⊢ A ⌞ ≤ ⌝ Σ' ⊣ Γ , T ↪ B
                 → ↑tmᶜ0 Σ ⇘ Σ'
                 → Γ ⊢ A ⌞ ≤ ⌝ Σ ⊣ Γ ↪ B
