module Implicit.Algo2Interm.Find where

open import Implicit.Language.All
open import Implicit.Interm.All
open import Implicit.Algo.All
open import Implicit.Algo2Interm.AlgoCounter.All

postulate
  ss-find-l : Γ ⊢ A ⌞ ≤⁺ ⌝ B ⊣ Δ
              → Γ ∋^ k
              → Δ ∋= k
              → k ε A

  ss-find-r : Γ ⊢ A ⌞ ≤⁻ ⌝ B ⊣ Δ
              → Γ ∋^ k
              → Δ ∋= k
              → k ε B

  s-find : Γ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B ↡ j
               → Γ ∋^ k
               → Δ ∋= k
               → find A k j

s-find0 : Γ ,^ ⊢ A ≤⁺ [ e' ]↝ Σ' ⊣ Δ ,= B ↪ C `→ D ↡ j
              → ↑tyᵉ0 e ⇘ e'
              → ↑tyᶜ0 Σ ⇘ Σ'
              → find A #0 j
s-find0 s up1 up2 = s-find s Z Z
