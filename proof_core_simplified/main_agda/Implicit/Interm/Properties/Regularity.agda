module Implicit.Interm.Properties.Regularity where

open import Implicit.Language.All
open import Implicit.Interm.Base

s-sregular : Γ ⊢ j # A ⌞ ≤ ⌝ B
           → SRegular Γ
s-sregular (s-refl regΔ cloA grd) = regΔ
s-sregular (s-int regΔ) = regΔ
s-sregular (s-var-∙ regΔ inΔ) = regΔ
s-sregular (s-arr₁ s s₁) = s-sregular s
s-sregular (s-arr₂ s s₁) = s-sregular s
s-sregular (s-arr₃ cloA grd s) = s-sregular s
s-sregular (s-∀ s) with s-sregular s
... | reg-S∙ r = r
s-sregular (s-∀l s ic fd upC upD) with s-sregular s
... | reg-S= r regA = r
s-sregular (s-∀l-no-appear s ic fd upC upD) with s-sregular s
... | reg-S^ r = r
s-sregular (s-svar-l x inΔ) = x
s-sregular (s-svar-r x inΔ) = x
s-sregular (s-svar-𝕚 _ x) = s-sregular x
s-sregular (s-svar-𝕔 _ x) = s-sregular x

t-tregular : Γ ⊢ j # e ⦂ A
           → TRegular Γ
t-tregular (⊢lit cloΓ) = cloΓ
t-tregular (⊢var cloΓ x∈Γ) = cloΓ
t-tregular (⊢ann ⊢e) = t-tregular ⊢e
t-tregular (⊢lam₁ ⊢e) with t-tregular ⊢e
... | reg-S, r regA = r
t-tregular (⊢lam₂ ⊢e) with t-tregular ⊢e
... | reg-S, r regA = r
t-tregular (⊢app₁ ⊢e ⊢e₁) = t-tregular ⊢e
t-tregular (⊢app₂ ⊢e ⊢e₁) = t-tregular ⊢e
t-tregular (⊢sub ⊢e B≤A x j≢Z) = t-tregular ⊢e
t-tregular (⊢tabs ⊢e) with t-tregular ⊢e
... | reg-S∙ r = r
t-tregular (⊢tabs-∞ ⊢e) with t-tregular ⊢e
... | reg-S∙ r = r
t-tregular {e = e ⓪ A} (⊢tapp ⊢e regA st s) = t-tregular ⊢e
