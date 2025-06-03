{-# OPTIONS --allow-unsolved-metas #-}
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
s+-polarity (s-∀l s ic fd upC upD upj) = ⊢r-strengthen=0 (s+-polarity s) (↑ty-arr upC upD)
s+-polarity (s-svar-l x inΔ) = ∋:=-⊢r x inΔ
s+-polarity (s-tapp s upj) = ⊢r-∀ (⊢r-◆0 (s+-polarity s))
s+-polarity (s-svar-𝕚 _ x) = s+-polarity x
s+-polarity (s-svar-𝕔 inΓ s) = s+-polarity s
s+-polarity (s-svar-𝕥 inΓ s) = s+-polarity s
s+-polarity (s-∀l-tail x ic tail upC upD upj) = {!!}

s--polarity (s-int regΔ) = ⊢r-int
s--polarity (s-var-∙ regΔ inΔ) = ⊢r-var-∙ inΔ
s--polarity (s-arr₁ s s₁) = ⊢r-arr (s+-polarity s) (s--polarity s₁)
s--polarity (s-∀ s) = ⊢r-∀ (s--polarity s)
s--polarity (s-svar-r x inΔ) = ∋:=-⊢r x inΔ


t-⊢r : Γ ⊢ j # e ⦂ A
     → Γ ⊢r A
t-⊢r (⊢lit regΓ) = ⊢r-int
t-⊢r (⊢var regΓ x∈Γ) = ∋⦂-⊢r regΓ x∈Γ
t-⊢r (⊢ann ⊢e) = t-⊢r ⊢e
t-⊢r (⊢lam₁ ⊢e) with t-tregular ⊢e
... | reg-S, r regA = ⊢r-arr regA (⊢r-strengthen,0 (t-⊢r ⊢e))
t-⊢r (⊢lam₂ ⊢e) with t-tregular ⊢e
... | reg-S, r regA = ⊢r-arr regA (⊢r-strengthen,0 (t-⊢r ⊢e))
t-⊢r (⊢app₁ ⊢e ⊢e₁) with t-⊢r ⊢e
... | ⊢r-arr r r₁ = r₁
t-⊢r (⊢app₂ ⊢e ⊢e₁) with t-⊢r ⊢e
... | ⊢r-arr r r₁ = r₁
t-⊢r (⊢sub ⊢e B≤A gc j≢Z) = ⊢r-𝕣' (s+-polarity B≤A)
t-⊢r (⊢tabs ⊢e) = ⊢r-∀ (t-⊢r ⊢e)
t-⊢r (⊢tapp ⊢e st) with t-⊢rʲ ⊢e
... | j-𝕥 r x = st0-⊢r (t-⊢r ⊢e) x st


s-⊢c-l : Γ ⊢ j # A ⌞ ≤ ⌝ B
        → Γ ⊢c A

s-⊢c-r : Γ ⊢ j # A ⌞ ≤ ⌝ B
        → Γ ⊢c B

s-⊢c-l {≤ = ≤⁺} (s-refl regΔ cloA grd) = cloA
s-⊢c-l {≤ = ≤⁺} (s-int regΔ) = ⊢c-int
s-⊢c-l {≤ = ≤⁺} (s-var-∙ regΔ inΔ) = ⊢c-var-∙ inΔ
s-⊢c-l {≤ = ≤⁺} (s-arr₁ s s₁) = ⊢c-arr (s-⊢c-r s) (s-⊢c-l s₁)
s-⊢c-l {≤ = ≤⁺} (s-arr₂ s s₁) = ⊢c-arr (s-⊢c-r s) (s-⊢c-l s₁)
s-⊢c-l {≤ = ≤⁺} (s-arr₃ cloA grd s) = ⊢c-arr cloA (s-⊢c-l s)
s-⊢c-l {≤ = ≤⁺} (s-∀ s) = ⊢c-∀ (s-⊢c-l s)
s-⊢c-l {≤ = ≤⁺} (s-∀l s ic fd upC upD upj) = ⊢c-∀ (⊢c-◆0 (s-⊢c-l s))
s-⊢c-l {≤ = ≤⁺} (s-tapp s upj) = ⊢c-∀ (⊢c-◆0 (s-⊢c-l s))
s-⊢c-l {≤ = ≤⁺} (s-svar-l x inΔ) = ⊢c-var-= (∋:=to∋= inΔ)
s-⊢c-l {≤ = ≤⁻} s = ⊢r-⊢c (s--polarity s)
s-⊢c-l {≤ = ≤⁺} (s-svar-𝕚 inΓ s) = ⊢c-var-= (∋:=to∋= inΓ)
s-⊢c-l {≤ = ≤⁺} (s-svar-𝕔 inΓ s) = ⊢c-var-= (∋:=to∋= inΓ)
s-⊢c-l {≤ = ≤⁺} (s-svar-𝕥 inΓ s) = ⊢c-var-= (∋:=to∋= inΓ)
s-⊢c-l {≤ = ≤⁺} (s-∀l-tail x ic tail upC upD upj) = {!!}

s-⊢c-r {≤ = ≤⁺} s = ⊢r-⊢c (s+-polarity s)
s-⊢c-r {≤ = ≤⁻} (s-int regΔ) = ⊢c-int
s-⊢c-r {≤ = ≤⁻} (s-var-∙ regΔ inΔ) = ⊢c-var-∙ inΔ
s-⊢c-r {≤ = ≤⁻} (s-arr₁ s s₁) = ⊢c-arr (s-⊢c-l s) (s-⊢c-r s₁)
s-⊢c-r {≤ = ≤⁻} (s-∀ s) = ⊢c-∀ (s-⊢c-r s)
s-⊢c-r {≤ = ≤⁻} (s-svar-r x inΔ) = ⊢c-var-= (∋:=to∋= inΔ)
