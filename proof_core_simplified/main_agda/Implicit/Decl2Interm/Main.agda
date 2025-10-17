module Implicit.Decl2Interm.Main where

open import Implicit.Language.All
import Implicit.Decl.All as D
import Implicit.Interm.All as I
open import Implicit.Decl.All
open import Implicit.Interm.All

⊢d-refl-eq : Γ ⊢d² `□ # A ≤ B
           → A ≡ B
⊢d-refl-eq (s-int regΔ) = refl
⊢d-refl-eq (s-var-∙ regΔ inΔ) = refl
⊢d-refl-eq (s-arr₁ s s₁) = cong₂ _`→_ (sym (⊢d-refl-eq s)) (⊢d-refl-eq s₁)
⊢d-refl-eq (s-∀ s) = cong `∀_ (⊢d-refl-eq s)

complete+ : Γ ⊢d² j # A% ≤ B
          → Γ ≫ A ⇘ A%
          → Γ ⊢ j # A ⌞ ≤⁺ ⌝ B


complete- : Γ ⊢d² `□ # A ≤ B%
          → Γ ≫ B ⇘ B%
          → Γ ⊢ `□ # A ⌞ ≤⁻ ⌝ B

complete+ (s-refl regΔ cloA) grd = s-refl regΔ (⊢r-≫-⊢c grd cloA) grd
complete+ (s-int regΔ) grd-int = s-int regΔ
complete+ (s-int regΔ) (grd-var= x) = s-svar-l x (s-int regΔ)
complete+ (s-var-∙ regΔ inΔ) (grd-var= x) = s-svar-l x (s-var-∙ regΔ inΔ)
complete+ (s-var-∙ regΔ inΔ) (grd-var∙ x) = s-var-∙ regΔ x
complete+ (s-arr₁ s s₁) (grd-var= x)
  with refl ← ⊢d-refl-eq s₁
  with refl ← ⊢d-refl-eq s = s-svar-l x (I.s-refl-∞ (s2-sregular s) (∋:=-⊢r (s2-sregular s) x))
complete+ (s-arr₁ s s₁) (grd-arr grd grd₁) = s-arr₁ (complete- s grd) (complete+ s₁ grd₁)
complete+ (s-arr₂ s s₁) (grd-var= x) = s-svar-l x (s-arr₂ (complete- s (⊢r-≫-eq (s2-⊢r-r s))) (complete+ s₁ (⊢r-≫-eq (s2-⊢r-l s₁))))
complete+ (s-arr₂ s s₁) (grd-arr grd grd₁) = s-arr₂ (complete- s grd) (complete+ s₁ grd₁)
complete+ (s-arr₃ regA s) (grd-var= x) = s-svar-l x (s-arr₃ (⊢r-⊢c regA) (⊢r-≫-eq regA) (complete+ s (⊢r-≫-eq (s2-⊢r-l s))))
complete+ (s-arr₃ regA s) (grd-arr grd grd₁) = s-arr₃ (⊢r-≫-⊢c grd regA) grd (complete+ s grd₁)
complete+ (s-∀ s) (grd-var= x)
  with refl ← ⊢d-refl-eq s = s-svar-l x (I.s-refl-∞ (s2-sregular (s-∀ s)) (∋:=-⊢r (s2-sregular (s-∀ s)) x))
complete+ (s-∀ s) (grd-∀ grd) = s-∀ (complete+ s grd)
complete+ (s-∀l grd₁ regA s fd upC upD) (grd-var= x)
  = s-svar-l x (s-∀l (complete+ s grd₁) fd upC upD)
complete+ (s-∀l-no-appear grd₁ regA s fd upC upD) (grd-var= x)
  = s-svar-l x (s-∀l-no-appear (complete+ s grd₁) fd upC upD)
complete+ (s-∀l grd₁ regA s fd upC upD) (grd-∀ grd)
  with reg-S= regΓ regA ← s2-sregular s
  = s-∀l (complete+ s (≫-trans0 regΓ regA grd₁ grd)) (find-≫-∙0 fd grd) upC upD
complete+ (s-∀l-no-appear grd₁ regA s fd upC upD) (grd-∀ grd)
  with reg-S^ regΓ ← s2-sregular s
  with ⟨ A' , upA ⟩ ← ↑ty-surjective fd
  with refl ← ⊢r-≫-eq' (⊢r-weaken^0 (⊢r-strengthen∙0 regA upA) upA) grd₁
  = s-∀l-no-appear (complete+ s (≫-trans'0 regΓ grd fd)) (¬ε-≫-∙0 fd grd) upC upD

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
