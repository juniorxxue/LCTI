module Implicit.Decl2Interm.Main where

open import Implicit.Language.All
open import Implicit.Decl.All
open import Implicit.Interm.All

⊢d-refl-eq : Γ ⊢d² ∞ # A ≤ B
           → A ≡ B
⊢d-refl-eq (s-int regΔ) = refl
⊢d-refl-eq (s-var-∙ regΔ inΔ) = refl
⊢d-refl-eq (s-arr₁ s s₁) = cong₂ _`→_ (sym (⊢d-refl-eq s)) (⊢d-refl-eq s₁)
⊢d-refl-eq (s-∀ s) = cong `∀_ (⊢d-refl-eq s)

complete+ : Γ ⊢d² j # A% ≤ B
          → Γ ≫ A ⇘ A%
          → Γ ⊢ j # A ⌞ ≤⁺ ⌝ B


complete- : Γ ⊢d² ∞ # A ≤ B%
          → Γ ≫ B ⇘ B%
          → Γ ⊢ ∞ # A ⌞ ≤⁻ ⌝ B

complete+ (s-refl regΔ cloA) grd = s-refl regΔ (⊢r-≫-⊢c grd cloA) grd
complete+ (s-int regΔ) grd-int = s-int regΔ
complete+ (s-int regΔ) (grd-var= x) = s-svar-l regΔ x
complete+ (s-var-∙ regΔ inΔ) (grd-var= x) = s-svar-l regΔ x
complete+ (s-var-∙ regΔ inΔ) (grd-var∙ x) = s-var-∙ regΔ x
complete+ (s-arr₁ s s₁) (grd-var= x)
  with refl ← ⊢d-refl-eq s₁
  with refl ← ⊢d-refl-eq s = s-svar-l (s2-sregular s) x
complete+ (s-arr₁ s s₁) (grd-arr grd grd₁) = s-arr₁ (complete- s grd) (complete+ s₁ grd₁)
complete+ (s-arr₂ s s₁) (grd-var= x) = s-svar-𝕚 x (s-arr₂ (complete- s (⊢r-≫-eq (s2-⊢r-r s))) (complete+ s₁ (⊢r-≫-eq (s2-⊢r-l s₁))))
complete+ (s-arr₂ s s₁) (grd-arr grd grd₁) = s-arr₂ (complete- s grd) (complete+ s₁ grd₁)
complete+ (s-arr₃ regA s) (grd-var= x) = s-svar-𝕔 x (s-arr₃ (⊢r-⊢c regA) (⊢r-≫-eq regA) (complete+ s (⊢r-≫-eq (s2-⊢r-l s))))
complete+ (s-arr₃ regA s) (grd-arr grd grd₁) = s-arr₃ (⊢r-≫-⊢c grd regA) grd (complete+ s grd₁)
complete+ (s-∀ s) (grd-var= x)
  with refl ← ⊢d-refl-eq s = s-svar-l (s2-sregular (s-∀ s)) x
complete+ (s-∀ s) (grd-∀ grd) = s-∀ (complete+ s grd)
complete+ (s-∀l grd₁ regA s case-𝕚 fd upC upD upj) (grd-var= x)
  = s-svar-𝕚 x (s-∀l (complete+ s grd₁) case-𝕚 fd upC upD upj)
complete+ (s-∀l grd₁ regA s case-𝕔 fd upC upD upj) (grd-var= x)
  = s-svar-𝕔 x (s-∀l (complete+ s grd₁) case-𝕔 fd upC upD upj)
complete+ (s-∀l-no-appear grd₁ regA s case-𝕚 fd upC upD upj) (grd-var= x)
  = s-svar-𝕚 x (s-∀l-no-appear (complete+ s grd₁) case-𝕚 fd upC upD upj)
complete+ (s-∀l-no-appear grd₁ regA s case-𝕔 fd upC upD upj) (grd-var= x)
  = s-svar-𝕔 x (s-∀l-no-appear (complete+ s grd₁) case-𝕔 fd upC upD upj)
complete+ (s-∀l grd₁ regA s case-𝕚 fd upC upD upj) (grd-∀ grd)
  with reg-S= regΓ regA ← s2-sregular s
  = s-∀l (complete+ s (≫-trans0 regΓ regA grd₁ grd)) case-𝕚 (find-≫-∙0 fd grd) upC upD upj
complete+ (s-∀l grd₁ regA s case-𝕔 fd upC upD upj) (grd-∀ grd)
  with reg-S= regΓ regA ← s2-sregular s
  = s-∀l (complete+ s (≫-trans0 regΓ regA grd₁ grd)) case-𝕔 (find-≫-∙0 fd grd) upC upD upj
complete+ (s-∀l-no-appear grd₁ regA s case-𝕚 fd upC upD upj) (grd-∀ grd)
  with reg-S^ regΓ ← s2-sregular s
  with ⟨ A' , upA ⟩ ← ↑ty-surjective fd
  with refl ← ⊢r-≫-eq' (⊢r-weaken^0 (⊢r-strengthen∙0 regA upA) upA) grd₁
  = s-∀l-no-appear (complete+ s (≫-trans'0 regΓ grd fd)) case-𝕚 (¬ε-≫-∙0 fd grd) upC upD upj
complete+ (s-∀l-no-appear grd₁ regA s case-𝕔 fd upC upD upj) (grd-∀ grd)
  with reg-S^ regΓ ← s2-sregular s
  with ⟨ A' , upA ⟩ ← ↑ty-surjective fd
  with refl ← ⊢r-≫-eq' (⊢r-weaken^0 (⊢r-strengthen∙0 regA upA) upA) grd₁
  = s-∀l-no-appear (complete+ s (≫-trans'0 regΓ grd fd)) case-𝕔 (¬ε-≫-∙0 fd grd) upC upD upj
complete+ (s-tapp x regA s upj) (grd-var= x₁) = s-svar-𝕥 x₁ (s-tapp (complete+ s x) upj)
complete+ (s-tapp x regA s upj) (grd-∀ grd)
  with reg-S= regΓ regA ← s2-sregular s = s-tapp (complete+ s (≫-trans0 regΓ regA x grd)) upj

complete- (s-int regΔ) grd-int = s-int regΔ
complete- (s-int regΔ) (grd-var= x) = s-svar-r regΔ x
complete- (s-var-∙ regΔ inΔ) (grd-var= x) = s-svar-r regΔ x
complete- (s-var-∙ regΔ inΔ) (grd-var∙ x) = s-var-∙ regΔ x
complete- (s-arr₁ s s₁) (grd-var= x)
  with refl ← ⊢d-refl-eq s₁
  with refl ← ⊢d-refl-eq s = s-svar-r (s2-sregular s) x
complete- (s-arr₁ s s₁) (grd-arr grd grd₁) = s-arr₁ (complete+ s grd) (complete- s₁ grd₁)
complete- (s-∀ s) (grd-var= x)
  with refl ← ⊢d-refl-eq s = s-svar-r (s2-sregular (s-∀ s)) x
complete- (s-∀ s) (grd-∀ grd) = s-∀ (complete- s grd)

complete0 : Γ ⊢d² j # A ≤ B
          → Γ ⊢ j # A ⌞ ≤⁺ ⌝ B
complete0 s = complete+ s (⊢r-≫-eq (s2-⊢r-l s))
