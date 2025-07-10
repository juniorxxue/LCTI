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
s-sregular (s-∀l s ic fd upC upD upj) with s-sregular s
... | reg-S= r regA = r
s-sregular (s-∀l-no-appear s ic fd upC upD upj) with s-sregular s
... | reg-S^ r = r
s-sregular (s-svar-l x inΔ) = s-sregular inΔ
s-sregular (s-svar-r x inΔ) = s-sregular inΔ
s-sregular (s-tapp s upj) with s-sregular s
... | reg-S= r regA = r
s-sregular (s-top+ regΔ cloA) = regΔ
s-sregular (s-top- regΔ regA) = regΔ
s-sregular (s-bot+ regΔ regA upj) = regΔ
s-sregular (s-bot- regΔ regA) = regΔ

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
t-tregular {e = e ⓪ A} (⊢tapp ⊢e st) = t-tregular ⊢e


⊢rʲ-strengthen=0 : Γ ,= T ⊢rʲ j'
                 → ↑tyʲ0 j ⇘ j'
                 → Γ ⊢rʲ j
⊢rʲ-strengthen=0 rj-Z ↑tyʲ-Z = rj-Z
⊢rʲ-strengthen=0 rj-∞ ↑tyʲ-∞ = rj-∞
⊢rʲ-strengthen=0 (rj-𝕚 regj) (↑tyʲ-𝕚 upj) = rj-𝕚 (⊢rʲ-strengthen=0 regj upj)
⊢rʲ-strengthen=0 (rj-𝕔 regj) (↑tyʲ-𝕔 upj) = rj-𝕔 (⊢rʲ-strengthen=0 regj upj)
⊢rʲ-strengthen=0 (rj-𝕥 regj x) (↑tyʲ-𝕥 upj upA) = rj-𝕥 (⊢rʲ-strengthen=0 regj upj) (⊢r-strengthen=0 x upA)

⊢rʲ-strengthen^0 : Γ ,^ ⊢rʲ j'
                 → ↑tyʲ0 j ⇘ j'
                 → Γ ⊢rʲ j
⊢rʲ-strengthen^0 rj-Z ↑tyʲ-Z = rj-Z
⊢rʲ-strengthen^0 rj-∞ ↑tyʲ-∞ = rj-∞
⊢rʲ-strengthen^0 (rj-𝕚 regj) (↑tyʲ-𝕚 upj) = rj-𝕚 (⊢rʲ-strengthen^0 regj upj)
⊢rʲ-strengthen^0 (rj-𝕔 regj) (↑tyʲ-𝕔 upj) = rj-𝕔 (⊢rʲ-strengthen^0 regj upj)
⊢rʲ-strengthen^0 (rj-𝕥 regj x) (↑tyʲ-𝕥 upj upA) = rj-𝕥 (⊢rʲ-strengthen^0 regj upj) (⊢r-strengthen^0 x upA)

⊢rʲ-strengthen,0 : Γ , T ⊢rʲ j
                 → Γ ⊢rʲ j
⊢rʲ-strengthen,0 rj-Z = rj-Z
⊢rʲ-strengthen,0 rj-∞ = rj-∞
⊢rʲ-strengthen,0 (rj-𝕚 regj) = rj-𝕚 (⊢rʲ-strengthen,0 regj)
⊢rʲ-strengthen,0 (rj-𝕔 regj) = rj-𝕔 (⊢rʲ-strengthen,0 regj)
⊢rʲ-strengthen,0 (rj-𝕥 regj x) = rj-𝕥 (⊢rʲ-strengthen,0 regj) (⊢r-strengthen,0 x)

s-⊢rʲ : Γ ⊢ j # A ⌞ ≤ ⌝ B
      → Γ ⊢rʲ j
s-⊢rʲ (s-refl regΔ cloA grd) = rj-Z
s-⊢rʲ (s-int regΔ) = rj-∞
s-⊢rʲ (s-var-∙ regΔ inΔ) = rj-∞
s-⊢rʲ (s-arr₁ s s₁) = s-⊢rʲ s
s-⊢rʲ (s-arr₂ s s₁) = rj-𝕚 (s-⊢rʲ s₁)
s-⊢rʲ (s-arr₃ cloA grd s) = rj-𝕔 (s-⊢rʲ s)
s-⊢rʲ (s-∀ s) = rj-∞
s-⊢rʲ (s-∀l s ic fd upC upD upj) = ⊢rʲ-strengthen=0 (s-⊢rʲ s) upj
s-⊢rʲ (s-∀l-no-appear s ic fd upC upD upj) = ⊢rʲ-strengthen^0 (s-⊢rʲ s) upj
s-⊢rʲ (s-tapp s upj) with s-sregular s
... | reg-S= r regA = rj-𝕥 (⊢rʲ-strengthen=0 (s-⊢rʲ s) upj) regA
s-⊢rʲ (s-svar-l x inΔ) = s-⊢rʲ inΔ
s-⊢rʲ (s-svar-r x inΔ) = rj-∞
s-⊢rʲ (s-top+ regΔ cloA) = rj-∞
s-⊢rʲ (s-top- regΔ regA) = rj-∞
s-⊢rʲ (s-bot+ regΔ regA regj) = regj
s-⊢rʲ (s-bot- regΔ regA) = rj-∞

⊢r-⋈ : Γ ⊢rʲ j
     → 𝕣 Γ ⊢rʲ j
⊢r-⋈ rj-Z = rj-Z
⊢r-⋈ rj-∞ = rj-∞
⊢r-⋈ (rj-𝕚 regj) = rj-𝕚 (⊢r-⋈ regj)
⊢r-⋈ (rj-𝕔 regj) = rj-𝕔 (⊢r-⋈ regj)
⊢r-⋈ (rj-𝕥 regj x) = rj-𝕥 (⊢r-⋈ regj) (⊢r-𝕣' x)


t-⊢rʲ : Γ ⊢ j # e ⦂ A
      → Γ ⊢rʲ j
t-⊢rʲ (⊢lit regΓ) = rj-Z
t-⊢rʲ (⊢var regΓ x∈Γ) = rj-Z
t-⊢rʲ (⊢ann ⊢e) = rj-Z
t-⊢rʲ (⊢lam₁ ⊢e) = rj-∞
t-⊢rʲ (⊢lam₂ ⊢e) = rj-𝕚 (⊢rʲ-strengthen,0 (t-⊢rʲ ⊢e))
t-⊢rʲ (⊢app₁ ⊢e ⊢e₁) with t-⊢rʲ ⊢e
... | rj-𝕔 r = r
t-⊢rʲ (⊢app₂ ⊢e ⊢e₁) with t-⊢rʲ ⊢e
... | rj-𝕚 r = r
t-⊢rʲ (⊢sub ⊢e B≤A gc j≢Z) = ⊢r-⋈ (s-⊢rʲ B≤A)
t-⊢rʲ (⊢tabs ⊢e) = rj-Z
t-⊢rʲ (⊢tapp ⊢e st) with t-⊢rʲ ⊢e
... | rj-𝕥 r x = r
