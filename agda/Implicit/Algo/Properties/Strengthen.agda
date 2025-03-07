module Implicit.Algo.Properties.Strengthen where

open import Implicit.Language.All
open import Implicit.Algo.Base


postulate
  s-strengthen=0 : Γ ,= T ⊢ A' ≤⁺ Σ' ⊣ Δ ,= T ↪ B'
                 → ↑ty0 B ⇘ B'
                 → ↑ty0 A ⇘ A'
                 → ↑tyᶜ0 Σ ⇘ Σ'
                 → Γ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B
