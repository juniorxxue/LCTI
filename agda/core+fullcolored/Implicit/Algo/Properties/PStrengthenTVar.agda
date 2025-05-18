module Implicit.Algo.Properties.PStrengthenTVar where

open import Implicit.Language.All
open import Implicit.Algo.Base
open import Implicit.Algo.Properties.Extension
open import Implicit.Algo.Properties.PShift
open import Implicit.Algo.Properties.Id
open import Implicit.Algo.Properties.PRegularity


postulate
  ◀,-⊆-total : Γ ⊆ Δ
             → Γ ◀ k ,⇘ Γ'
             → ∃[ Δ' ](Δ ◀ k ,⇘ Δ')

postulate
  inst-strengthen, : [ A / X ] Γ ⟹ Δ
                   → Γ ◀ k ,⇘ Γ'
                   → Δ ◀ k ,⇘ Δ'
                   → [ A / X ] Γ' ⟹ Δ'

postulate
  ss-strengthen, : Γ ⊢ A ⌞ ≤ ⌝ B ⊣ Δ
                 → Γ ◀ k ,⇘ Γ'
                 → Δ ◀ k ,⇘ Δ'
                 → Γ' ⊢ A ⌞ ≤ ⌝ B ⊣ Δ'

postulate
  t-strengthen, : Γ ⊢ Σ' ⇒ e' ⇒ A
                → Γ ◀ k ,⇘ Γ'
                → Σ ↑tmᶜ k ⇘ Σ'
                → e ↑tm k ⇘ e'
                → Γ' ⊢ Σ ⇒ e ⇒ A

postulate
  s-strengthen, : Γ ⊢ A ≤⁺ Σ' ⊣ Δ ↪ B
                → Γ ◀ k ,⇘ Γ'
                → Δ ◀ k ,⇘ Δ'
                → Σ ↑tmᶜ k ⇘ Σ'
                → Γ' ⊢ A ≤⁺ Σ ⊣ Δ' ↪ B

postulate
  s-strengthen,0 : Γ , T ⋈ ⊢ A ≤⁺ Σ' ⊣ Δ , T ⋈  ↪ B
                   → ↑tmᶜ0 Σ ⇘ Σ'
                   → Γ ⋈ ⊢ A ≤⁺ Σ ⊣ Δ ⋈ ↪ B
