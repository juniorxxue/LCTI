module Implicit.Interm.Ground where

open import Implicit.Language.All
open import Implicit.Interm.Base

s+-≫ : Γ ⊢ ∞ # A ⌞ ≤⁺ ⌝ B
     → Γ ≫ A ⇘ B

s--≫ : Γ ⊢ ∞ # A ⌞ ≤⁻ ⌝ B
     → Γ ≫ B ⇘ A

s+-≫ (s-int cloΓ) = grd-int
s+-≫ (s-var-∙ cloΓ inΓ) = grd-var∙ inΓ
s+-≫ (s-arr₁ s s₁) = grd-arr (s--≫ s) (s+-≫ s₁)
s+-≫ (s-∀ s) = grd-∀ (s+-≫ s)
s+-≫ (s-var-sub-l cloA inΓ) = grd-var= inΓ

s--≫ (s-int cloΓ) = grd-int
s--≫ (s-var-∙ cloΓ inΓ) = grd-var∙ inΓ
s--≫ (s-arr₁ s s₁) = grd-arr (s+-≫ s) (s--≫ s₁)
s--≫ (s-∀ s) = grd-∀ (s--≫ s)
s--≫ (s-var-sub-r cloA inΓ) = grd-var= inΓ
