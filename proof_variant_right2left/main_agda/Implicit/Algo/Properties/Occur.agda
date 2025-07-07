module Implicit.Algo.Properties.Occur where

open import Implicit.Language.All
open import Implicit.Algo.Base

εᶜ-↑tyᶜ : k₁ εᶜ Σ
        → Σ ↑tyᶜ k₂ ⇘ Σ'
        → k₂ #≤ k₁
        → #S k₁ εᶜ Σ'
εᶜ-↑tyᶜ (^∈-type inA) (↑tyᶜ-τ up-t) sm = ^∈-type (ε-↑ty inA up-t sm)
εᶜ-↑tyᶜ (^∈-term kεᶜ) (↑tyᶜ-e up-e upc) sm = ^∈-term (εᶜ-↑tyᶜ kεᶜ upc sm)

εᶜ-↑tyᶜ0 : k εᶜ Σ
        → ↑tyᶜ0 Σ ⇘ Σ'
        → #S k εᶜ Σ'
εᶜ-↑tyᶜ0 k-in up-c = εᶜ-↑tyᶜ k-in up-c z≤n
