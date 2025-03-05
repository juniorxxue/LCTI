module Implicit.Algo.Properties.Extension where

open import Implicit.Language.All
open import Implicit.Algo.Base

inst-⊆ : [ A / X ] Γ ⟹ Δ
       → Γ ⊆ Δ
inst-⊆ (⟹^0 up regA env) = evar-sol {!⊆-refl!} regA
inst-⊆ (⟹^S inst up1) = evar (inst-⊆ inst)
inst-⊆ (⟹∙S inst up1) = uvar (inst-⊆ inst)
inst-⊆ (⟹=S inst up1 regB) = svar (inst-⊆ inst) regB

s-⊆ : Γ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B
    → Γ ⊆ Δ
s-⊆ (s-empty regΓ cloA x) = {!!}
s-⊆ (s-type ss) = {!!}
s-⊆ (s-term-c cloA ap ⊢e s) = s-⊆ s
s-⊆ (s-term-o opnA ⊢e x s) = {!!}
s-⊆ (s-∀l s upᶜ upᵉ upC upD) = {!!}
