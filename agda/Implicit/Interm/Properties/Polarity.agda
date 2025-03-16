module Implicit.Interm.Properties.Polarity where

open import Implicit.Language.All
open import Implicit.Interm.Base
open import Implicit.Interm.Properties.Regularity

s+-polarity : Γ ⊢ j # A ⌞ ≤⁺ ⌝ B
            → Γ ⊢r B

s--polarity : Γ ⊢ j # A ⌞ ≤⁻ ⌝ B
            → Γ ⊢r A

s+-polarity (s-refl regΔ cloA grd) = ⊢c-≫-⊢r regΔ cloA grd
s+-polarity (s-int regΔ) = ⊢r-int
s+-polarity (s-var-∙ regΔ inΔ) = ⊢r-var-∙ inΔ
s+-polarity (s-arr₁ s s₁) = ⊢r-arr (s--polarity s) (s+-polarity s₁)
s+-polarity (s-arr₂ s s₁) = ⊢r-arr (s--polarity s) (s+-polarity s₁)
s+-polarity (s-arr₃ cloA grd s) = ⊢r-arr (⊢c-≫-⊢r (s-sregular s) cloA grd) (s+-polarity s)
s+-polarity (s-∀ s) = ⊢r-∀ (s+-polarity s)
s+-polarity (s-∀l s ic fd upC upD) = ⊢r-strengthen=0 (s+-polarity s) (↑ty-arr upC upD)
s+-polarity (s-svar-l x inΔ) = ∋:=-⊢r x inΔ

s--polarity (s-int regΔ) = ⊢r-int
s--polarity (s-var-∙ regΔ inΔ) = ⊢r-var-∙ inΔ
s--polarity (s-arr₁ s s₁) = ⊢r-arr (s+-polarity s) (s--polarity s₁)
s--polarity (s-∀ s) = ⊢r-∀ (s--polarity s)
s--polarity (s-svar-r x inΔ) = ∋:=-⊢r x inΔ
