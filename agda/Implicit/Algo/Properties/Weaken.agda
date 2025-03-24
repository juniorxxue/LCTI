module Implicit.Algo.Properties.Weaken where

open import Implicit.Language.All
open import Implicit.Algo.Base
open import Implicit.Algo.Properties.WeakenEVar public


postulate

  s-weaken,0 : Γ ⋈ ⊢ A ≤⁺ Σ ⊣ Δ ⋈ ↪ B
           → ↑tmᶜ0 Σ ⇘ Σ'
           → Γ ⊢r T
           → Γ , T ⋈ ⊢ A ≤⁺ Σ' ⊣ Δ , T ⋈  ↪ B

  t-weaken,0 : Γ ⊢ Σ ⇒ e ⇒ A
             → ↑tmᶜ0 Σ ⇘ Σ'
             → ↑tm0 e ⇘ e'
             → Γ ⊢r T
             → Γ , T ⊢ Σ' ⇒ e' ⇒ A

  s-weaken=0 : Γ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B
             → ↑ty0 A ⇘ A'
             → ↑tyᶜ0 Σ ⇘ Σ'
             → ↑ty0 B ⇘ B'
             → Γ ,= T ⊢ A' ≤⁺ Σ' ⊣ Δ ,= T ↪ B'
