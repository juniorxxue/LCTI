module Implicit.Interm2Algo.Inst where

open import Implicit.Language.All
open import Implicit.Algo.All

s-unsol-sol : Γ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B
            → Δ ∋ k := T
            → [ T / k ] Γ ⟹ Γ'
            → Γ' ⊢ A ≤⁺ Σ ⊣ Δ ↪ B
s-unsol-sol (s-empty regΓ cloA grd) inΔ inst = {!!}
s-unsol-sol (s-type ss) inΔ inst = {!!}
s-unsol-sol (s-term-c cloA ap ⊢e s) inΔ inst = {!!}
s-unsol-sol (s-term-o opnA ⊢e ss s) inΔ inst = {!!}
s-unsol-sol (s-∀l-y pk s upᶜ upᵉ upC upD) inΔ inst = {!!}
s-unsol-sol (s-∀l-n-y ¬pk s upᶜ upᵉ upC upD) inΔ inst = {!!}
s-unsol-sol (s-∀l-n-n ¬pk s upᶜ upᵉ upC upD) inΔ inst = {!!}
s-unsol-sol (s-tapp s upᶜ) inΔ inst = {!!}
s-unsol-sol (s-svar-term x s) inΔ inst = {!!}
s-unsol-sol (s-svar-tapp x s) inΔ inst = {!!}
s-unsol-sol (s-evar-infers infs inst₁) inΔ inst = {!!}


s-unsol-sol0 : Γ ,^ ⊢ A ≤⁺ Σ ⊣ Δ ,= B ↪ C
             → Γ ,= B ⊢ A ≤⁺ Σ ⊣ Δ ,= B ↪ C
s-unsol-sol0 {B = B} s
  with ⟨ B' , upB ⟩ ← ↑ty0-total B
  with reg-S= regA regA₁ ← s-env-out s
  = s-unsol-sol s (Z upB) (⟹^0 upB {!!} {!!})
