module Implicit.Algo.Properties.PStrengthenSVar where

open import Implicit.Language.All
open import Implicit.Algo.Base
open import Implicit.Algo.Properties.Extension
open import Implicit.Algo.Properties.PShift
open import Implicit.Algo.Properties.Id
open import Implicit.Algo.Properties.Regularity

postulate
  ◀=-unique : Γ ◀ k =⇘ Γ'
            → Γ ◀ k =⇘ Δ'
            → Γ' ≡ Δ'

postulate
  ◀=-⊆-total : Γ ⊆ Δ
             → Γ ◀ k =⇘ Γ'
             → ∃[ Δ' ](Δ ◀ k =⇘ Δ')

postulate
  inst-strengthen= : [ B' / punchIn k X ] Γ ⟹ Δ
                   → Γ ◀ k =⇘ Γ'
                   → Δ ◀ k =⇘ Δ'
                   → B ↑ty k ⇘ B'
                   → [ B / X ] Γ' ⟹ Δ'

postulate
  ss-strengthen= : Γ ⊢ A' ⌞ ≤ ⌝ B' ⊣ Δ
                 → Γ ◀ k =⇘ Γ'
                 → Δ ◀ k =⇘ Δ'
                 → A ↑ty k ⇘ A'
                 → B ↑ty k ⇘ B'
                 → Γ' ⊢ A ⌞ ≤ ⌝ B ⊣ Δ'

postulate
  ◀=-𝕣 : Γ ◀ k =⇘ Γ'
       → 𝕣 Γ ◀ k =⇘ 𝕣 Γ'

postulate
  t-strengthen= : Γ ⊢ Σ' ⇒ e' ⇒ A'
                → Γ ◀ k =⇘ Γ'
                → A ↑ty k ⇘ A'
                → e ↑tyᵉ k ⇘ e'
                → Σ ↑tyᶜ k ⇘ Σ'
                → Γ' ⊢ Σ ⇒ e ⇒ A

postulate
  s-strengthen= : Γ ⊢ A' ≤⁺ Σ' ⊣ Δ ↪ B'
                → Γ ◀ k =⇘ Γ'
                → Δ ◀ k =⇘ Δ'
                → A ↑ty k ⇘ A'
                → B ↑ty k ⇘ B'
                → Σ ↑tyᶜ k ⇘ Σ'
                → Γ' ⊢ A ≤⁺ Σ ⊣ Δ' ↪ B

postulate
  s-strengthen=0 : Γ ,= T ⊢ A' ≤⁺ Σ' ⊣ Δ ,= T ↪ B'
                   → ↑ty0 B ⇘ B'
                   → ↑ty0 A ⇘ A'
                   → ↑tyᶜ0 Σ ⇘ Σ'
                   → Γ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B
