{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --allow-incomplete-matches #-}
module Implicit.Algo.Properties.Weaken where

open import Implicit.Language.All
open import Implicit.Algo.Base
-- open import Implicit.Algo.Properties.Extension
open import Implicit.Algo.Properties.Shift
open import Implicit.Algo.Properties.Id

ss-weaken : Γ ⊢ A ⌞ ≤ ⌝ B ⊣ Δ
          → Γ ⨟ Δ ▶ k ⇘ Γ' ⨟ Δ' w/ mA
          → A ↑ty k ⇘ A'
          → B ↑ty k ⇘ B'
          → Γ' ⊢ A' ⌞ ≤ ⌝ B' ⊣ Δ'
ss-weaken (s-int regΓ) new ↑ty-int ↑ty-int = {!!}
ss-weaken (s-var-∙ regΓ inΔ) new upA upB = {!!}
ss-weaken (s-ex-l^ inst) new upA upB = {!!}
ss-weaken (s-ex-r^ inst) new upA upB = {!!}
ss-weaken (s-ex-l= regΓ x-in) new upA upB = {!!}
ss-weaken (s-ex-r= regΓ x-in) new upA upB = {!!}
ss-weaken (s-arr s s₁) new upA upB = {!!}
ss-weaken (s-∀ s) new upA upB = {!!}


postulate
  t-weaken : Γ ⊢ Σ ⇒ e ⇒ A
          → Γ ▶ k ⇘ Γ' w/ mA
          → Σ ↑tyᶜ k ⇘ Σ'
          → e ↑tyᵉ k ⇘ e'
          → A ↑ty k ⇘ A'
          → Γ' ⊢ Σ' ⇒ e' ⇒ A'

  infs-weaken : Γ ⊨ Σ ⟹ A
             → Γ ▶ k ⇘ Γ' w/ mA
             → Σ ↑tyᶜ k ⇘ Σ'
             → A ↑ty k ⇘ A'
             → Γ' ⊨ Σ' ⟹ A'


  s-weaken : Γ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B
          → Γ ⨟ Δ ▶ k ⇘ Γ' ⨟ Δ' w/ mA
          → A ↑ty k ⇘ A'
          → Σ ↑tyᶜ k ⇘ Σ'
          → B ↑ty k ⇘ B'
          → Γ' ⊢ A' ≤⁺ Σ' ⊣ Δ' ↪ B'


t-weaken^0 : Γ ⊢ Σ ⇒ e ⇒ A
           → ↑tyᶜ0 Σ ⇘ Σ'
           → ↑tyᵉ0 e ⇘ e'
           → ↑ty0 A ⇘ A'
           → Γ ,^ ⊢ Σ' ⇒ e' ⇒ A'
t-weaken^0 ⊢e upΣ upe upA = t-weaken ⊢e ▶Z^ upΣ upe upA

s-weaken^0 : Γ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B
           → ↑ty0 A ⇘ A'
           → ↑tyᶜ0 Σ ⇘ Σ'
           → ↑ty0 B ⇘ B'
           → Γ ,^ ⊢ A' ≤⁺ Σ' ⊣ Δ ,^ ↪ B'
s-weaken^0 s upA upΣ upB = s-weaken s ▶Z^ upA upΣ upB

s-weaken∙0 : Γ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B
           → ↑ty0 A ⇘ A'
           → ↑tyᶜ0 Σ ⇘ Σ'
           → ↑ty0 B ⇘ B'
           → Γ ,∙ ⊢ A' ≤⁺ Σ' ⊣ Δ ,∙ ↪ B'
s-weaken∙0 s upA upΣ upB = s-weaken s ▶Z∙ upA upΣ upB

s-weaken=0 : Γ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B
           → ↑ty0 A ⇘ A'
           → ↑tyᶜ0 Σ ⇘ Σ'
           → ↑ty0 B ⇘ B'
           → Γ ⊢r T
           → Γ ,= T ⊢ A' ≤⁺ Σ' ⊣ Δ ,= T ↪ B'
s-weaken=0 s upA upΣ upB regT = s-weaken s (▶Z= regT) upA upΣ upB
