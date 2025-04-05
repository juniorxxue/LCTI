module Implicit.Algo.Properties.Polarity where

open import Implicit.Language.All
open import Implicit.Algo.Base
open import Implicit.Algo.Properties.Extension

ss-polarity+ : Γ ⊢ A ⌞ ≤⁺ ⌝ B ⊣ Δ
             → Γ ⊢r B
ss-polarity- : Γ ⊢ A ⌞ ≤⁻ ⌝ B ⊣ Δ
             → Γ ⊢r A

ss-polarity+ (s-int regΓ) = ⊢r-int
ss-polarity+ (s-var-∙ regΓ x) = ⊢r-var-∙ x
ss-polarity+ (s-ex-l^ inst) = inst-⊢r inst
ss-polarity+ (s-ex-l= regΓ x-in) = ∋:=-⊢r regΓ x-in
ss-polarity+ (s-arr s s₁) = ⊢r-arr (ss-polarity- s) (⊆-⊢r' (ss-polarity+ s₁) (ss-⊆ s))
ss-polarity+ (s-∀ s) = ⊢r-∀ (ss-polarity+ s)
ss-polarity+ (s-var-≝ regΓ x) = ⊢r-var-≝ x
ss-polarity+ (s-def-l= regΓ x-in) = ∋:≝-⊢r regΓ x-in

ss-polarity- (s-int regΓ) = ⊢r-int
ss-polarity- (s-var-∙ regΓ x) = ⊢r-var-∙ x
ss-polarity- (s-ex-r^ inst) = inst-⊢r inst
ss-polarity- (s-ex-r= regΓ x-in) = ∋:=-⊢r regΓ x-in
ss-polarity- (s-arr s s₁) = ⊢r-arr (ss-polarity+ s) (⊆-⊢r' (ss-polarity- s₁) (ss-⊆ s))
ss-polarity- (s-∀ s) = ⊢r-∀ (ss-polarity- s)
ss-polarity- (s-var-≝ regΓ x) = ⊢r-var-≝ x
ss-polarity- (s-def-r= regΓ x-in) = ∋:≝-⊢r regΓ x-in

ss-polarity+-out : Γ ⊢ A ⌞ ≤⁺ ⌝ B ⊣ Δ
                 → Δ ⊢r B
ss-polarity+-out s = ⊆-⊢r (ss-polarity+ s) (ss-⊆ s)

ss-polarity--out : Γ ⊢ A ⌞ ≤⁻ ⌝ B ⊣ Δ
                 → Δ ⊢r A
ss-polarity--out s = ⊆-⊢r (ss-polarity- s) (ss-⊆ s)
