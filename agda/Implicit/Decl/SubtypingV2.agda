module Implicit.Decl.SubtypingV2 where

open import Implicit.Language.All

----------------------------------------------------------------------
--+                           Subtyping                            +--
----------------------------------------------------------------------

infix 3 _⊢_#_⌞_⌝_
data _⊢_#_⌞_⌝_ : Env n m → Counter m → Type m → Polar → Type m → Set where
  s-refl :
      (regΔ : SRegular Δ)
    → (cloA : Δ ⊢r A)
    → Δ ⊢ Z # A ⌞ ≤⁺ ⌝ A
  s-int :
      (regΔ : SRegular Δ)
    → Δ ⊢ ∞ # Int ⌞ ≤ ⌝ Int
  s-var-∙ :
      (regΔ : SRegular Δ)
    → (inΔ : Δ ∋∙ X)
    → Δ ⊢ ∞ # ‶ X ⌞ ≤ ⌝ ‶ X
  s-arr₁ :
      Δ ⊢ ∞ # C ⌞ ⋆ ≤ ⌝ A
    → Δ ⊢ ∞ # B ⌞ ≤ ⌝ D
    → Δ ⊢ ∞ # A `→ B ⌞ ≤ ⌝ C `→ D
  s-arr₂ :
      Δ ⊢ ∞ # C ⌞ ≤⁻ ⌝ A
    → Δ ⊢ j # B ⌞ ≤⁺ ⌝ D
    → Δ ⊢ 𝕚 j # A `→ B ⌞ ≤⁺ ⌝ C `→ D
  s-arr₃ :
      (regA : Δ ⊢r A)
    → Δ ⊢ j # B ⌞ ≤⁺ ⌝ D
    → Δ ⊢ 𝕔 j # A `→ B ⌞ ≤⁺ ⌝ A `→ D
  s-∀ :
      Δ ,∙ ⊢ ∞ # A ⌞ ≤ ⌝ B
    → Δ ⊢ ∞ # `∀ A ⌞ ≤ ⌝ `∀ B
  s-∀l :
      (grd : (Γ ,= B) ≫ A ⇘ A%)
    → (regA : Γ ,∙ ⊢r A)
    → Γ ,= B ⊢ j' # A% ⌞ ≤⁺ ⌝ C' `→ D'
    → (ic : (𝕚𝕔 j))
    → (fd : find A #0 j')
    → (upC : ↑ty0 C ⇘ C')
    → (upD : ↑ty0 D ⇘ D')
    → (upj : ↑tyʲ0 j ⇘ j')
    → Γ ⊢ j # `∀ A ⌞ ≤⁺ ⌝ C `→ D
  s-tapp :
      (Δ ,= B) ≫ A ⇘ A%
    → (regA : Δ ,∙ ⊢r A)
    → Δ ,= B ⊢ j' # A% ⌞ ≤⁺ ⌝ C
    → (upj : ↑tyʲ0 j ⇘ j')
    → Δ ⊢ 𝕥₍ B ₎ j # `∀ A ⌞ ≤⁺ ⌝ `∀ C



s2-sregular : Γ ⊢ j # A ⌞ ≤ ⌝ B
            → SRegular Γ
s2-sregular (s-refl regΔ cloA) = regΔ
s2-sregular (s-int regΔ) = regΔ
s2-sregular (s-var-∙ regΔ inΔ) = regΔ
s2-sregular (s-arr₁ s s₁) = s2-sregular s
s2-sregular (s-arr₂ s s₁) = s2-sregular s
s2-sregular (s-arr₃ regA s) = s2-sregular s
s2-sregular (s-∀ s) with s2-sregular s
... | reg-S∙ r = r
s2-sregular (s-∀l grd regA s ic fd upC upD upj) with s2-sregular s
... | reg-S= r regA = r
s2-sregular (s-tapp x regA s upj) with s2-sregular s
... | reg-S= r regA = r


s2-⊢r-l : Γ ⊢ j # A ⌞ ≤ ⌝ B
        → Γ ⊢r A

postulate
  s2-⊢r-r : Γ ⊢ j # A ⌞ ≤ ⌝ B
         → Γ ⊢r B

  s2-weaken=0 : Γ ⊢ j # A ⌞ ≤ ⌝ B
            → ↑ty0 A ⇘ A'
            → ↑ty0 B ⇘ B'
            → ↑tyʲ0 j ⇘ j'
            → Γ ⊢r T
            → Γ ,= T ⊢ j' # A' ⌞ ≤ ⌝ B'

s2-⊢r-l (s-refl regΔ cloA) = cloA
s2-⊢r-l (s-int regΔ) = ⊢r-int
s2-⊢r-l (s-var-∙ regΔ inΔ) = ⊢r-var-∙ inΔ
s2-⊢r-l (s-arr₁ s s₁) = ⊢r-arr (s2-⊢r-r s) (s2-⊢r-l s₁)
s2-⊢r-l (s-arr₂ s s₁) = ⊢r-arr (s2-⊢r-r s) (s2-⊢r-l s₁)
s2-⊢r-l (s-arr₃ regA s) = ⊢r-arr regA (s2-⊢r-l s)
s2-⊢r-l (s-∀ s) = ⊢r-∀ (s2-⊢r-l s)
s2-⊢r-l (s-∀l grd regA s ic fd upC upD upj) = ⊢r-∀ regA
s2-⊢r-l (s-tapp x regA s upj) = ⊢r-∀ regA
