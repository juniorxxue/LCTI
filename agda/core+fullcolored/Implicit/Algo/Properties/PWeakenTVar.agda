module Implicit.Algo.Properties.PWeakenTVar where

open import Implicit.Language.All
open import Implicit.Algo.Base
open import Implicit.Algo.Properties.Extension
open import Implicit.Algo.Properties.PShift
open import Implicit.Algo.Properties.Id


postulate
  ss-weaken, : Γ ⊢ A ⌞ ≤ ⌝ B ⊣ Δ
             → Γ ⨟ Δ ▶s k , T ⇘ Γ' ⨟ Δ'
             → Γ' ⊢ A ⌞ ≤ ⌝ B ⊣ Δ'

postulate
  t-weaken, : Γ ⊢ Σ ⇒ e ⇒ A
            → Γ ▶ k , T ⇘ Γ'
            → Σ ↑tmᶜ k ⇘ Σ'
            → e ↑tm k ⇘ e'
            → Γ' ⊢ Σ' ⇒ e' ⇒ A

postulate
  s-weaken, : Γ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B
            → Σ ↑tmᶜ k ⇘ Σ'
            → Γ ⨟ Δ ▶s k , T ⇘ Γ' ⨟ Δ'
            → Γ' ⊢ A ≤⁺ Σ' ⊣ Δ' ↪ B

postulate
  s-weaken,0 : Γ ⋈ ⊢ A ≤⁺ Σ ⊣ Δ ⋈ ↪ B
             → ↑tmᶜ0 Σ ⇘ Σ'
             → Γ ⊢r T
             → Γ , T ⋈ ⊢ A ≤⁺ Σ' ⊣ Δ , T ⋈  ↪ B

postulate
  t-weaken,0 : Γ ⊢ Σ ⇒ e ⇒ A
             → ↑tmᶜ0 Σ ⇘ Σ'
             → ↑tm0 e ⇘ e'
             → Γ ⊢r T
             → Γ , T ⊢ Σ' ⇒ e' ⇒ A
