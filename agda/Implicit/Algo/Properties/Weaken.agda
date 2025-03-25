module Implicit.Algo.Properties.Weaken where

open import Implicit.Language.All
open import Implicit.Algo.Base
open import Implicit.Algo.Properties.WeakenEVar public
open import Implicit.Algo.Properties.WeakenTVar public

postulate

  s-weaken=0 : Γ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B
             → ↑ty0 A ⇘ A'
             → ↑tyᶜ0 Σ ⇘ Σ'
             → ↑ty0 B ⇘ B'
             → Γ ,= T ⊢ A' ≤⁺ Σ' ⊣ Δ ,= T ↪ B'
