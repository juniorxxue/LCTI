module Implicit.Interm2Algo2.Extra where

open import Implicit.Language.All
open import Implicit.Algo.All
open import Implicit.Interm.Base
open import Implicit.Interm.Properties.Regularity
open import Implicit.Interm.Properties.Polarity
open import Implicit.Interm.Ground
open import Implicit.Interm2Algo2.Counter2Context
open import Implicit.Interm2Algo2.ExtIrrev
open import Implicit.Interm2Algo2.EnvDiff
open import Implicit.Interm2Algo2.OpenClose
open import Implicit.Interm2Algo2.Find


postulate
  ⅆ-⊆/c : Δ ⅆ Δ' ≋ Γ ⅆ Γ'
     → Γ' ⊆ Δ' w/t A w/c j
     → Γ ⊆ Δ w/t A w/c j

  s-subirrev-final : Ψ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B
                 → Δ ⅆ Ω ≋ Ψ ⅆ Γ
                 → Ω ⊢c A
                 → Γ ⊢ A ≤⁺ Σ ⊣ Ω ↪ B
