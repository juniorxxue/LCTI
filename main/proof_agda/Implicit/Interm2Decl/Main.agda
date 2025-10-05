module Implicit.Interm2Decl.Main where

open import Implicit.Language.All
import Implicit.Decl.All as D
import Implicit.Interm.All as I
open import Implicit.Decl.All
open import Implicit.Interm.All

open import Implicit.Interm2Decl.AuxLemmas

sound : Γ ⊢ j # A ⌞ ≤ ⌝ B
      → Γ ≫ A ⇘ A%
      → Γ ≫ B ⇘ B%
      → Γ ⊢d² j # A% ≤ B%
sound (s-refl regΔ cloA grd) grd1 grd2
  with refl ← ≫-unique grd1 grd
  with refl ← ⊢r-≫-eq' (⊢c-≫-⊢r regΔ cloA grd1) grd2 = s-refl regΔ (⊢c-≫-⊢r regΔ cloA grd)
sound (s-int regΔ) grd-int grd-int = s-int regΔ
sound (s-var-∙ regΔ inΔ) (grd-var= x) (grd-var= x₁) = ⊥-elim (∋∙-∋:=-false inΔ x₁)
sound (s-var-∙ regΔ inΔ) (grd-var= x) (grd-var∙ x₁) = ⊥-elim (∋∙-∋:=-false inΔ x)
sound (s-var-∙ regΔ inΔ) (grd-var∙ x) (grd-var= x₁) = ⊥-elim (∋∙-∋:=-false inΔ x₁)
sound (s-var-∙ regΔ inΔ) (grd-var∙ x) (grd-var∙ x₁) = s-var-∙ regΔ x₁
sound (s-arr₁ s s₁) (grd-arr grd1 grd3) (grd-arr grd2 grd4) = s-arr₁ (sound s grd2 grd1) (sound s₁ grd3 grd4)
sound (s-arr₂ s s₁) (grd-arr grd1 grd3) (grd-arr grd2 grd4) = s-arr₂ (sound s grd2 grd1) (sound s₁ grd3 grd4)
sound (s-arr₃ cloA grd s) (grd-arr grd1 grd3) (grd-arr grd2 grd4)
  with refl ← ≫-unique grd grd1
  with regA ← ⊢c-≫-⊢r (I.s-sregular s) cloA grd
  with refl ← ⊢r-≫-eq' regA grd2 = s-arr₃ regA (sound s grd3 grd4)
sound (s-∀ s) (grd-∀ grd1) (grd-∀ grd2) = s-∀ (sound s grd1 grd2)
sound s'@(s-∀l {B = B} s ic fd upC upD upj) (grd-∀ grd1) grdCD@(grd-arr grd2 grd3)
  with cloA ← s-⊢c-l s
  with ⟨ A% , grdA ⟩ ← ≫-total (I.s-sregular s) cloA
  with reg-S= regΓ regA ← I.s-sregular s
  with regCD ← s+-polarity s'
  with refl ← ⊢r-≫-eq' regCD grdCD
  = s-∀l (≫-trans'' (reg-S∙ regΓ) grd1 (∙⟹^0 (proj₂ (↑ty0-total B)) regA) Z∙ grdA)
         (⊢c-≫-⊢r (reg-S∙ regΓ) (⊢c-◆0 (s-⊢c-l s)) grd1)
         (sound s grdA (⊢r-≫-eq (s+-polarity s)))
         ic
         (find-≫-∙' fd Z∙ Z grd1)
         upC
         upD
         upj
sound s'@(s-∀l-no-appear s ic fd upC upD upj) (grd-∀ grd1) grdCD@(grd-arr grd2 grd3)
  with cloA ← s-⊢c-l s
  with ⟨ A% , grdA ⟩ ← ≫-total (I.s-sregular s) cloA
  with reg-S^ regΓ ← I.s-sregular s
  with regCD ← s+-polarity s'
  with refl ← ⊢r-≫-eq' regCD grdCD
  with refl ← ≫-same grd1 ◈Z grdA fd
  = s-∀l-no-appear (⊢r-≫-eq (⊢c-≫-⊢r (reg-S^ regΓ) cloA grdA))
         (⊢c-≫-⊢r (reg-S∙ regΓ) (⊢c-◇0 (s-⊢c-l s)) grd1)
         (sound s grdA (⊢r-≫-eq (s+-polarity s)))
         ic
         (¬ε-≫-∙' fd Z Z∙ grd1)
         upC
         upD
         upj
sound (s-tapp {B = B} s upj) (grd-∀ grd1) (grd-∀ grd2)
  with cloA ← s-⊢c-l s
  with ⟨ A% , grdA ⟩ ← ≫-total (I.s-sregular s) cloA
  with reg-S= regΓ regA ← I.s-sregular s
  with refl ← ⊢r-≫-eq' (⊢r-◆0 (s+-polarity s)) grd2
  = s-tapp (≫-trans'' (reg-S∙ regΓ) grd1 (∙⟹^0 (proj₂ (↑ty0-total B)) regA) Z∙ grdA)
           (⊢c-≫-⊢r (reg-S∙ regΓ) (⊢c-◆0 cloA) grd1)
           (sound s grdA (⊢r-≫-eq (s+-polarity s))) upj
sound (s-svar-l x inΔ) (grd-var= x₁) grd2
  with refl ← ∋:=-unique inΔ x₁
  with regA ← ∋:=-⊢r x inΔ
  with refl ← ⊢r-≫-eq' regA grd2
  = sd-refl-∞ x regA
sound (s-svar-l x inΔ) (grd-var∙ x₁) grd2 = ⊥-elim (∋∙-∋:=-false x₁ inΔ)
sound (s-svar-r x inΔ) grd1 (grd-var= x₁)
  with refl ← ∋:=-unique inΔ x₁
  with regA ← ∋:=-⊢r x inΔ
  with refl ← ⊢r-≫-eq' regA grd1 = sd-refl-∞ x regA
sound (s-svar-r x inΔ) grd1 (grd-var∙ x₁) = ⊥-elim (∋∙-∋:=-false x₁ inΔ)
sound (s-svar-𝕚 inΓ s) (grd-var= x) (grd-arr grd2 grd3)
  with refl ← ∋:=-unique inΓ x = sound s (⊢r-≫-eq (∋:=-⊢r (I.s-sregular s) inΓ)) (grd-arr grd2 grd3)
sound (s-svar-𝕚 inΓ s) (grd-var∙ x) (grd-arr grd2 grd3) = ⊥-elim (∋∙-∋:=-false x inΓ)
sound (s-svar-𝕔 inΓ s) (grd-var= x) (grd-arr grd2 grd3)
  with refl ← ∋:=-unique inΓ x = sound s (⊢r-≫-eq (∋:=-⊢r (I.s-sregular s) inΓ)) (grd-arr grd2 grd3)
sound (s-svar-𝕔 inΓ s) (grd-var∙ x) grd2 = ⊥-elim (∋∙-∋:=-false x inΓ)
sound (s-svar-𝕥 inΓ s) (grd-var= x) (grd-∀ grd2)
  with refl ← ∋:=-unique inΓ x = sound s (⊢r-≫-eq (∋:=-⊢r (I.s-sregular s) inΓ)) (grd-∀ grd2)
sound (s-svar-𝕥 inΓ s) (grd-var∙ x) grd2 = ⊥-elim (∋∙-∋:=-false x inΓ)
