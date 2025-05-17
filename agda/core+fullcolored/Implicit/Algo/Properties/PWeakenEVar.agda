module Implicit.Algo.Properties.PWeakenEVar where

open import Implicit.Language.All
open import Implicit.Algo.Base
open import Implicit.Algo.Properties.Extension
open import Implicit.Algo.Properties.PShift
open import Implicit.Algo.Properties.Id


postulate
  ss-weaken^ : Γ ⊢ A ⌞ ≤ ⌝ B ⊣ Δ
             → Γ ⨟ Δ ▶ k ,^⇘ Γ' ⨟ Δ'
             → A ↑ty k ⇘ A'
             → B ↑ty k ⇘ B'
             → Γ' ⊢ A' ⌞ ≤ ⌝ B' ⊣ Δ'

postulate
  ▶^-𝕣 : Γ ▶ k ,^⇘ Γ'
       → 𝕣 Γ ▶ k ,^⇘ 𝕣 Γ'

postulate
  t-weaken^ : Γ ⊢ Σ ⇒ e ⇒ A
            → Γ ▶ k ,^⇘ Γ'
            → Σ ↑tyᶜ k ⇘ Σ'
            → e ↑tyᵉ k ⇘ e'
            → A ↑ty k ⇘ A'
            → Γ' ⊢ Σ' ⇒ e' ⇒ A'

postulate
  s-weaken^ : Γ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B
            → Γ ⨟ Δ ▶ k ,^⇘ Γ' ⨟ Δ'
            → A ↑ty k ⇘ A'
            → Σ ↑tyᶜ k ⇘ Σ'
            → B ↑ty k ⇘ B'
            → Γ' ⊢ A' ≤⁺ Σ' ⊣ Δ' ↪ B'

postulate
  t-weaken^0 : Γ ⊢ Σ ⇒ e ⇒ A
             → ↑tyᶜ0 Σ ⇘ Σ'
             → ↑tyᵉ0 e ⇘ e'
             → ↑ty0 A ⇘ A'
             → Γ ,^ ⊢ Σ' ⇒ e' ⇒ A'

postulate
  s-weaken^0 : Γ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B
             → ↑ty0 A ⇘ A'
             → ↑tyᶜ0 Σ ⇘ Σ'
             → ↑ty0 B ⇘ B'
             → Γ ,^ ⊢ A' ≤⁺ Σ' ⊣ Δ ,^ ↪ B'
