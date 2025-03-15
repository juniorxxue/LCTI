module Implicit.Algo2Interm.Main where

open import Implicit.Language.All
open import Implicit.Interm.All
open import Implicit.Algo.All
open import Implicit.Algo2Interm.AlgoCounter.All
open import Implicit.Algo2Interm.Context2Counter


tc-~ : Γ ⊢ Σ ⇒ e ⇒ A ↡ j
     → Γ ⊢ ⟨ j , A ⟩ ~t Σ

sc-~ : Γ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B ↡ j
     → Δ ⊢ ⟨ j , B ⟩ ~s Σ

sound : Γ ⊢ Σ ⇒ e ⇒ A ↡ j
      → Γ ⊢ j # e ⦂ A

sound-s : Γ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B ↡ j
        → Δ ⊢ j # A ⌞ ≤⁺ ⌝ B

sound-ss : Γ ⊢ A ⌞ ≤ ⌝ B ⊣ Δ
         → Δ ⊢ ∞ # A ⌞ ≤ ⌝ B


tc-~ ⊢e = {!!}
