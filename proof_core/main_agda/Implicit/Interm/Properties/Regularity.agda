module Implicit.Interm.Properties.Regularity where

open import Implicit.Language.All hiding (_⊢rʲ_)
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
s-sregular (s-∀l s ic fd upC upD upj) with s-sregular s
... | reg-S= r regA = r
s-sregular (s-∀l-no-appear s ic fd upC upD upj) with s-sregular s
... | reg-S^ r = r
s-sregular (s-svar-l x inΔ) = x
s-sregular (s-svar-r x inΔ) = x
s-sregular (s-tapp s upj) with s-sregular s
... | reg-S= r regA = r
s-sregular (s-svar-𝕚 _ x) = s-sregular x
s-sregular (s-svar-𝕔 _ x) = s-sregular x
s-sregular (s-svar-𝕥 x x₁) = s-sregular x₁

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
t-tregular {e = e ⓪ A} (⊢tapp ⊢e st) = t-tregular ⊢e



infix 3 _⊢rʲ_
data _⊢rʲ_ : Env n m → Counter m → Set where
  j-Z : Γ ⊢rʲ Z
  j-∞ : Γ ⊢rʲ ∞
  j-𝕚 : Γ ⊢rʲ j
      → Γ ⊢rʲ (𝕚 j)
  j-𝕔 : Γ ⊢rʲ j
      → Γ ⊢rʲ (𝕔 j)
  j-𝕥 : Γ ⊢rʲ j
      → Γ ⊢r A
      → Γ ⊢rʲ 𝕥₍ A ₎ j

⊢rʲ-strengthen=0 : Γ ,= T ⊢rʲ j'
                 → ↑tyʲ0 j ⇘ j'
                 → Γ ⊢rʲ j
⊢rʲ-strengthen=0 j-Z ↑tyʲ-Z = j-Z
⊢rʲ-strengthen=0 j-∞ ↑tyʲ-∞ = j-∞
⊢rʲ-strengthen=0 (j-𝕚 regj) (↑tyʲ-𝕚 upj) = j-𝕚 (⊢rʲ-strengthen=0 regj upj)
⊢rʲ-strengthen=0 (j-𝕔 regj) (↑tyʲ-𝕔 upj) = j-𝕔 (⊢rʲ-strengthen=0 regj upj)
⊢rʲ-strengthen=0 (j-𝕥 regj x) (↑tyʲ-𝕥 upj upA) = j-𝕥 (⊢rʲ-strengthen=0 regj upj) (⊢r-strengthen=0 x upA)

⊢rʲ-strengthen^0 : Γ ,^ ⊢rʲ j'
                 → ↑tyʲ0 j ⇘ j'
                 → Γ ⊢rʲ j
⊢rʲ-strengthen^0 j-Z ↑tyʲ-Z = j-Z
⊢rʲ-strengthen^0 j-∞ ↑tyʲ-∞ = j-∞
⊢rʲ-strengthen^0 (j-𝕚 regj) (↑tyʲ-𝕚 upj) = j-𝕚 (⊢rʲ-strengthen^0 regj upj)
⊢rʲ-strengthen^0 (j-𝕔 regj) (↑tyʲ-𝕔 upj) = j-𝕔 (⊢rʲ-strengthen^0 regj upj)
⊢rʲ-strengthen^0 (j-𝕥 regj x) (↑tyʲ-𝕥 upj upA) = j-𝕥 (⊢rʲ-strengthen^0 regj upj) (⊢r-strengthen^0 x upA)

⊢rʲ-strengthen,0 : Γ , T ⊢rʲ j
                 → Γ ⊢rʲ j
⊢rʲ-strengthen,0 j-Z = j-Z
⊢rʲ-strengthen,0 j-∞ = j-∞
⊢rʲ-strengthen,0 (j-𝕚 regj) = j-𝕚 (⊢rʲ-strengthen,0 regj)
⊢rʲ-strengthen,0 (j-𝕔 regj) = j-𝕔 (⊢rʲ-strengthen,0 regj)
⊢rʲ-strengthen,0 (j-𝕥 regj x) = j-𝕥 (⊢rʲ-strengthen,0 regj) (⊢r-strengthen,0 x)

s-⊢rʲ : Γ ⊢ j # A ⌞ ≤ ⌝ B
      → Γ ⊢rʲ j
s-⊢rʲ (s-refl regΔ cloA grd) = j-Z
s-⊢rʲ (s-int regΔ) = j-∞
s-⊢rʲ (s-var-∙ regΔ inΔ) = j-∞
s-⊢rʲ (s-arr₁ s s₁) = s-⊢rʲ s
s-⊢rʲ (s-arr₂ s s₁) = j-𝕚 (s-⊢rʲ s₁)
s-⊢rʲ (s-arr₃ cloA grd s) = j-𝕔 (s-⊢rʲ s)
s-⊢rʲ (s-∀ s) = j-∞
s-⊢rʲ (s-∀l s ic fd upC upD upj) = ⊢rʲ-strengthen=0 (s-⊢rʲ s) upj
s-⊢rʲ (s-∀l-no-appear s ic fd upC upD upj) = ⊢rʲ-strengthen^0 (s-⊢rʲ s) upj
s-⊢rʲ (s-tapp s upj) with s-sregular s
... | reg-S= r regA = j-𝕥 (⊢rʲ-strengthen=0 (s-⊢rʲ s) upj) regA
s-⊢rʲ (s-svar-l x inΔ) = j-∞
s-⊢rʲ (s-svar-r x inΔ) = j-∞
s-⊢rʲ (s-svar-𝕚 _ x) = s-⊢rʲ x
s-⊢rʲ (s-svar-𝕔 _ x) = s-⊢rʲ x
s-⊢rʲ (s-svar-𝕥 x x₁) = s-⊢rʲ x₁

⊢r-⋈ : Γ ⊢rʲ j
     → 𝕣 Γ ⊢rʲ j
⊢r-⋈ j-Z = j-Z
⊢r-⋈ j-∞ = j-∞
⊢r-⋈ (j-𝕚 regj) = j-𝕚 (⊢r-⋈ regj)
⊢r-⋈ (j-𝕔 regj) = j-𝕔 (⊢r-⋈ regj)
⊢r-⋈ (j-𝕥 regj x) = j-𝕥 (⊢r-⋈ regj) (⊢r-𝕣' x)


t-⊢rʲ : Γ ⊢ j # e ⦂ A
      → Γ ⊢rʲ j
t-⊢rʲ (⊢lit regΓ) = j-Z
t-⊢rʲ (⊢var regΓ x∈Γ) = j-Z
t-⊢rʲ (⊢ann ⊢e) = j-Z
t-⊢rʲ (⊢lam₁ ⊢e) = j-∞
t-⊢rʲ (⊢lam₂ ⊢e) = j-𝕚 (⊢rʲ-strengthen,0 (t-⊢rʲ ⊢e))
t-⊢rʲ (⊢app₁ ⊢e ⊢e₁) with t-⊢rʲ ⊢e
... | j-𝕔 r = r
t-⊢rʲ (⊢app₂ ⊢e ⊢e₁) with t-⊢rʲ ⊢e
... | j-𝕚 r = r
t-⊢rʲ (⊢sub ⊢e B≤A gc j≢Z) = ⊢r-⋈ (s-⊢rʲ B≤A)
t-⊢rʲ (⊢tabs ⊢e) = j-Z
t-⊢rʲ (⊢tabs-∞ ⊢e) = j-∞
t-⊢rʲ (⊢tapp ⊢e st) with t-⊢rʲ ⊢e
... | j-𝕥 r x = r
