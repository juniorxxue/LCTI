module Implicit.Algo.Properties.PWeakenSVar where

open import Implicit.Language.All
open import Implicit.Algo.Base
open import Implicit.Algo.Properties.Extension
open import Implicit.Algo.Properties.PShift
open import Implicit.Algo.Properties.Id


postulate
  ss-weaken= : Γ ⊢ A ⌞ ≤ ⌝ B ⊣ Δ
             → Γ ⨟ Δ ▶ k ,= T ⇘ Γ' ⨟ Δ'
             → A ↑ty k ⇘ A'
             → B ↑ty k ⇘ B'
             → Γ' ⊢ A' ⌞ ≤ ⌝ B' ⊣ Δ'

postulate
  t-weaken= : Γ ⊢ Σ ⇒ e ⇒ A
            → Γ ▶ k ,= T ⇘ Γ'
            → Σ ↑tyᶜ k ⇘ Σ'
            → e ↑tyᵉ k ⇘ e'
            → A ↑ty k ⇘ A'
            → Γ' ⊢ Σ' ⇒ e' ⇒ A'

postulate
  s-weaken= : Γ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B
            → Γ ⨟ Δ ▶ k ,= T ⇘ Γ' ⨟ Δ'
            → A ↑ty k ⇘ A'
            → Σ ↑tyᶜ k ⇘ Σ'
            → B ↑ty k ⇘ B'
            → Γ' ⊢ A' ≤⁺ Σ' ⊣ Δ' ↪ B'

postulate
  s-weaken=0 : Γ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B
             → ↑ty0 A ⇘ A'
             → ↑tyᶜ0 Σ ⇘ Σ'
             → ↑ty0 B ⇘ B'
             → Γ ⊢r T
             → Γ ,= T ⊢ A' ≤⁺ Σ' ⊣ Δ ,= T ↪ B'
