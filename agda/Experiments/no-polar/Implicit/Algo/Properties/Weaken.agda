module Implicit.Algo.Properties.Weaken where

open import Implicit.Language
open import Implicit.Algo.Base

postulate

  s-weaken, : Γ ⊢ A ⌞ ≤ ⌝ Σ ⊣ Δ ↪ B
            → Γ ▶ k , T ⇘ Γ'
            → Δ ▶ k , T ⇘ Δ'
            → Σ ↑tmᶜ k ⇘ Σ'
            → Γ' ⊢ A  ⌞ ≤ ⌝ Σ' ⊣ Δ' ↪ B
{-
s-weaken, s-int newΓ newΔ ↑tmᶜ-τ = {!!} -- unique
s-weaken, (s-empty clo) newΓ newΔ ↑tmᶜ-□ = {!!} -- unique
s-weaken, s-var newΓ newΔ ↑tmᶜ-τ = {!!} -- unique
s-weaken, (s-ex-l^ x-in inst) newΓ newΔ ↑tmᶜ-τ = s-ex-l^ {!!} {!!} -- ext prv; inst prv
s-weaken, (s-ex-l= x-in s) newΓ newΔ ↑tmᶜ-τ = s-ex-l= {!!} (s-weaken, s newΓ newΔ ↑tmᶜ-τ)
s-weaken, (s-ex-r^ x-in inst) newΓ newΔ upΣ = {!!}
s-weaken, (s-ex-r= x-in s) newΓ newΔ upΣ = {!!}
s-weaken, (s-arr s s₁) newΓ newΔ upΣ = {!!}
s-weaken, (s-term-c ⊢e s) newΓ newΔ upΣ = {!!}
s-weaken, (s-term-o opnA ⊢e s s₁) newΓ newΔ (↑tmᶜ-e up-e upΣ) =
  s-term-o {!!} {!!} (s-weaken, s newΓ {!!} ↑tmᶜ-τ) (s-weaken, s₁ {!!} newΔ upΣ)
s-weaken, {T = T} (s-∀ s) newΓ newΔ ↑tmᶜ-τ = let ⟨ T' , upT ⟩ = ↑ty0-total T
                                             in s-∀ (s-weaken, s (▶S∙ newΓ upT) (▶S∙ newΔ upT) ↑tmᶜ-τ)
s-weaken, {T = T} (s-∀l s upᶜ upᵉ st₁ st₂) newΓ newΔ (↑tmᶜ-e up-e upΣ) =
  s-∀l (s-weaken, s (▶S^ newΓ {!!}) (▶S= newΔ {!!}) (↑tmᶜ-e {!!} {!!})) {!!} {!!} st₁ st₂
-}

s-weaken,0 : Γ ⊢ A ⌞ ≤ ⌝ Σ ⊣ Δ ↪ B
           → ↑tmᶜ0 Σ ⇘ Σ'
           → Γ ⊢c T
           → Δ ⊢c T
           → Γ , T ⊢ A ⌞ ≤ ⌝ Σ' ⊣ Δ , T ↪ B
s-weaken,0 s upΣ cloT cloT' = s-weaken, s (▶Z cloT) (▶Z cloT') upΣ
