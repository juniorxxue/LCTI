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
s-⊆ (s-tapp s upᶜ) with s-⊆ s
... | svar r regA = r
s-⊆ (s-svar-term inΓ s) = s-⊆ s
s-⊆ (s-svar-tapp inΓ s) = s-⊆ s
s-⊆ (s-evar-infers x inst) = inst-⊆ inst

inst-⊆/x : [ A / X ] Γ ⟹ Δ
         → Γ ⊆ Δ w/v X
inst-⊆/x (⟹^0 up regA env) = ext-Z^ env regA
inst-⊆/x (⟹^S inst up1) = ext-S^ (inst-⊆/x inst)
inst-⊆/x (⟹∙S inst up1) = ext-S∙ (inst-⊆/x inst)
inst-⊆/x (⟹=S inst up1 regB) = ext-S= (inst-⊆/x inst) regB


ss+-⊆/ : Γ ⊢ A ⌞ ≤⁺ ⌝ B ⊣ Δ
       → Γ ⊆ Δ w/t A

ss--⊆/ : Γ ⊢ A ⌞ ≤⁻ ⌝ B ⊣ Δ
      → Γ ⊆ Δ w/t B

ss+-⊆/ (s-int regΓ) = ext-int regΓ
ss+-⊆/ (s-var-∙ regΓ x) = ext-var (⊆/x-refl regΓ (⊢c-var-∙ x))
ss+-⊆/ (s-ex-l^ inst) = ext-var (inst-⊆/x inst)
ss+-⊆/ (s-ex-l= regΓ x-in) = ext-var (⊆/x-refl regΓ (⊢c-var-= (∋:=to∋= x-in)))
ss+-⊆/ (s-arr s s₁) = ext-arr (ss--⊆/ s) (ss+-⊆/ s₁)
ss+-⊆/ (s-∀ s) = ext-∀ (ss+-⊆/ s)

ss--⊆/ (s-int regΓ) = ext-int regΓ
ss--⊆/ (s-var-∙ regΓ x) = ext-var (⊆/x-refl regΓ (⊢c-var-∙ x))
ss--⊆/ (s-ex-r^ inst) = ext-var (inst-⊆/x inst)
ss--⊆/ (s-ex-r= regΓ x-in) = ext-var (⊆/x-refl regΓ (⊢c-var-= (∋:=to∋= x-in)))
ss--⊆/ (s-arr s s₁) = ext-arr (ss+-⊆/ s) (ss--⊆/ s₁)
ss--⊆/ (s-∀ s) = ext-∀ (ss--⊆/ s)
