module Implicit.Algo.Properties.Strengthen where

open import Implicit.Language.All
open import Implicit.Algo.Base
open import Implicit.Algo.Properties.Extension
open import Implicit.Algo.Properties.Shift
open import Implicit.Algo.Properties.Id
open import Implicit.Algo.Properties.Regularity

ss-strengthen : Γ ⊢ A' ⌞ ≤ ⌝ B' ⊣ Δ
               → Γ ⨟ Δ ◀ k ⇘ Γ' ⨟ Δ'
               → A ↑ty k ⇘ A'
               → B ↑ty k ⇘ B'
               → Γ' ⊢ A ⌞ ≤ ⌝ B ⊣ Δ'
ss-strengthen (s-int regΓ) new upA upB = {!!}
ss-strengthen (s-var-∙ regΓ inΔ) new upA upB = {!!}
ss-strengthen (s-ex-l^ inst) new upA upB = {!!}
ss-strengthen (s-ex-r^ inst) new upA upB = {!!}
ss-strengthen (s-ex-l= regΓ x-in) new upA upB = {!!}
ss-strengthen (s-ex-r= regΓ x-in) new upA upB = {!!}
ss-strengthen (s-arr ss ss₁) new upA upB = {!!}
ss-strengthen (s-∀ ss) new upA upB = {!!}



t-strengthen : Γ ⊢ Σ' ⇒ e' ⇒ A'
              → Γ ◀ k ⇘ Γ'
              → A ↑ty k ⇘ A'
              → e ↑tyᵉ k ⇘ e'
              → Σ ↑tyᶜ k ⇘ Σ'
              → Γ' ⊢ Σ ⇒ e ⇒ A
t-strengthen = {!!}

infs-strengthen : Γ ⊨ Σ' ⟹ A'
                 → Γ ◀ k ⇘ Γ'
                 → A ↑ty k ⇘ A'
                 → Σ ↑tyᶜ k ⇘ Σ'
                 → Γ' ⊨ Σ ⟹ A
infs-strengthen = {!!}

s-strengthen : Γ ⊢ A' ≤⁺ Σ' ⊣ Δ ↪ B'
              → Γ ⨟ Δ ◀ k ⇘ Γ' ⨟ Δ'
              → A ↑ty k ⇘ A'
              → B ↑ty k ⇘ B'
              → Σ ↑tyᶜ k ⇘ Σ'
              → Γ' ⊢ A ≤⁺ Σ ⊣ Δ' ↪ B
s-strengthen = {!!}

-- corollaries
s-strengthen=0 : Γ ,= T ⊢ A' ≤⁺ Σ' ⊣ Δ ,= T ↪ B'
                 → ↑ty0 A ⇘ A'
                 → ↑ty0 B ⇘ B'
                 → ↑tyᶜ0 Σ ⇘ Σ'
                 → Γ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B
s-strengthen=0 s upA upB upΣ = s-strengthen s ◀Z= upA upB upΣ

s-strengthen^0 : Γ ,^ ⊢ A' ≤⁺ Σ' ⊣ Δ ,^ ↪ B'
                 → ↑ty0 A ⇘ A'
                 → ↑ty0 B ⇘ B'
                 → ↑tyᶜ0 Σ ⇘ Σ'
                 → Γ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B
s-strengthen^0 s upA upB upΣ = s-strengthen s ◀Z^ upA upB upΣ
