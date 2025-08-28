module Implicit.Interm2Algo.Inst where

open import Implicit.Language.All
open import Implicit.Algo.All

ss-unsol-sol : Γ ⊢ A ⌞ ≤ ⌝ B ⊣ Δ
             → Δ ∋ k := T
             → [ T / k ] Γ ⟹ Γ'
             → Γ' ⊢ A ⌞ ≤ ⌝ B ⊣ Δ


s-unsol-sol : Γ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B
            → Δ ∋ k := T
            → [ T / k ] Γ ⟹ Γ'
            → Γ' ⊢ A ≤⁺ Σ ⊣ Δ ↪ B
s-unsol-sol (s-empty regΓ cloA grd) inΔ inst = ⊥-elim (∋^-∋=-false (inst-∋^ inst) (∋:=to∋= inΔ))
s-unsol-sol (s-type ss) inΔ inst = s-type {!!}
s-unsol-sol (s-term-c cloA ap ⊢e s) inΔ inst = s-term-c {!!} {!!} {!!} (s-unsol-sol s inΔ inst)
s-unsol-sol (s-term-o opnA ⊢e ss s) inΔ inst = s-term-c {!!} {!!} {!subsumption0 ⊢e!} {!!}
s-unsol-sol {T = T} (s-∀l-y pk upB s upᶜ upᵉ upC upD) inΔ inst
  with ⟨ T' , upT ⟩ ← ↑ty0-total T
  with reg-S= r regA ← s-env-in s
  = s-∀l-y pk upB (s-unsol-sol s (S= inΔ upT) (⟹=S inst upT regA)) upᶜ upᵉ upC upD
s-unsol-sol {T = T} (s-∀l-n-y ¬pk s upᶜ upᵉ upC upD) inΔ inst
  with ⟨ T' , upT ⟩ ← ↑ty0-total T
  = s-∀l-n-y ¬pk (s-unsol-sol s (S= inΔ upT) (⟹^S inst upT)) upᶜ upᵉ upC upD
s-unsol-sol {T = T} (s-∀l-n-n ¬pk s upᶜ upᵉ upC upD) inΔ inst
  with ⟨ T' , upT ⟩ ← ↑ty0-total T
  = s-∀l-n-n ¬pk (s-unsol-sol s (S^ inΔ upT) (⟹^S inst upT)) upᶜ upᵉ upC upD
s-unsol-sol {T = T} (s-tapp s upᶜ) inΔ inst
  with ⟨ T' , upT ⟩ ← ↑ty0-total T
  with reg-S= r regA ← s-env-in s
  = s-tapp (s-unsol-sol s (S= inΔ upT) (⟹=S inst upT regA)) upᶜ
s-unsol-sol (s-svar-term x s) inΔ inst = ⊥-elim (∋^-∋=-false (inst-∋^ inst) (∋:=to∋= inΔ))
s-unsol-sol (s-svar-tapp x s) inΔ inst = ⊥-elim (∋^-∋=-false (inst-∋^ inst) (∋:=to∋= inΔ))
s-unsol-sol (s-evar-infers infs inst₁) inΔ inst = s-evar-infers {!!} {!!}

s-unsol-sol0 : Γ ,^ ⊢ A ≤⁺ Σ ⊣ Δ ,= B ↪ C
             → Γ ,= B ⊢ A ≤⁺ Σ ⊣ Δ ,= B ↪ C
s-unsol-sol0 {B = B} s
  with ⟨ B' , upB ⟩ ← ↑ty0-total B
  with reg-S= regA regA₁ ← s-env-out s
  = s-unsol-sol s (Z upB) (⟹^0 upB {!!} {!!})
