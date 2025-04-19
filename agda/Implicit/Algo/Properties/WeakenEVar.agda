module Implicit.Algo.Properties.WeakenEVar where

open import Implicit.Language.All
open import Implicit.Algo.Base
open import Implicit.Algo.Properties.Extension
open import Implicit.Algo.Properties.Shift
open import Implicit.Algo.Properties.Id

postulate

  ss-weaken^ : Γ ⊢ A ⌞ ≤ ⌝ B ⊣ Δ
           → Γ ⨟ Δ ▶ k ,^⇘ Γ' ⨟ Δ'
           → A ↑ty k ⇘ A'
           → B ↑ty k ⇘ B'
           → Γ' ⊢ A' ⌞ ≤ ⌝ B' ⊣ Δ'


  t-weaken^ : Γ ⊢ Σ ⇒ e ⇒ A
          → Γ ▶ k ,^⇘ Γ'
          → Σ ↑tyᶜ k ⇘ Σ'
          → e ↑tyᵉ k ⇘ e'
          → A ↑ty k ⇘ A'
          → Γ' ⊢ Σ' ⇒ e' ⇒ A'

  s-weaken^ : Γ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B
          → Γ ⨟ Δ ▶ k ,^⇘ Γ' ⨟ Δ'
          → A ↑ty k ⇘ A'
          → Σ ↑tyᶜ k ⇘ Σ'
          → B ↑ty k ⇘ B'
          → Γ' ⊢ A' ≤⁺ Σ' ⊣ Δ' ↪ B'

t-weaken^0 : Γ ⊢ Σ ⇒ e ⇒ A
           → ↑tyᶜ0 Σ ⇘ Σ'
           → ↑tyᵉ0 e ⇘ e'
           → ↑ty0 A ⇘ A'
           → Γ ,^ ⊢ Σ' ⇒ e' ⇒ A'
t-weaken^0 ⊢e upΣ upe upA = t-weaken^ ⊢e ▶Z upΣ upe upA

s-weaken^0 : Γ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B
           → ↑ty0 A ⇘ A'
           → ↑tyᶜ0 Σ ⇘ Σ'
           → ↑ty0 B ⇘ B'
           → Γ ,^ ⊢ A' ≤⁺ Σ' ⊣ Δ ,^ ↪ B'
s-weaken^0 s upA upΣ upB = s-weaken^ s ▶Z upA upΣ upB
