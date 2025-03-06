module Implicit.Algo.Properties.Extension where

open import Implicit.Language.All
open import Implicit.Algo.Base

inst-⊆ : [ A / X ] Γ ⟹ Δ
       → Γ ⊆ Δ
inst-⊆ (⟹^0 up regA env) = evar-sol (⊆-refl env) regA
inst-⊆ (⟹^S inst up1) = evar (inst-⊆ inst)
inst-⊆ (⟹∙S inst up1) = uvar (inst-⊆ inst)
inst-⊆ (⟹=S inst up1 regB) = svar (inst-⊆ inst) regB

ss-⊆ : Γ ⊢ A ⌞ ≤ ⌝ B ⊣ Δ
     → Γ ⊆ Δ
ss-⊆ (s-int regΓ) = ⊆-refl regΓ
ss-⊆ (s-var-∙ regΓ x) = ⊆-refl regΓ
ss-⊆ (s-ex-l^ inst) = inst-⊆ inst
ss-⊆ (s-ex-r^ inst) = inst-⊆ inst
ss-⊆ (s-ex-l= regΓ x-in) = ⊆-refl regΓ
ss-⊆ (s-ex-r= regΓ x-in) = ⊆-refl regΓ
ss-⊆ (s-arr s s₁) = ⊆-trans (ss-⊆ s) (ss-⊆ s₁)
ss-⊆ (s-∀ s) with ss-⊆ s
... | uvar r = r

s-⊆ : Γ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B
    → Γ ⊆ Δ
s-⊆ (s-empty regΓ cloA x) = ⊆-refl regΓ
s-⊆ (s-type ss) = ss-⊆ ss
s-⊆ (s-term-c cloA ap ⊢e s) = s-⊆ s
s-⊆ (s-term-o opnA ⊢e x s) = ⊆-trans (ss-⊆ x) (s-⊆ s)
s-⊆ (s-∀l s upᶜ upᵉ upC upD) with s-⊆ s
... | evar-sol r regA = r

⊆-regular : SRegular Γ
          → Γ ⊆ Δ
          → SRegular Δ
⊆-regular (reg-Z regΓ) (mark x) = reg-Z regΓ
⊆-regular (reg-S∙ regΓ) (uvar ext) = reg-S∙ (⊆-regular regΓ ext)
⊆-regular (reg-S^ regΓ) (evar ext) = reg-S^ (⊆-regular regΓ ext)
⊆-regular (reg-S^ regΓ) (evar-sol ext regA) = reg-S= (⊆-regular regΓ ext) regA
⊆-regular (reg-S= regΓ regA) (svar ext regA₁) = reg-S= (⊆-regular regΓ ext) (⊆-⊢r regA ext)
