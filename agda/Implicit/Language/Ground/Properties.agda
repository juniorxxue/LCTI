module Implicit.Language.Ground.Properties where

open import Implicit.Language.Base
open import Implicit.Language.Shift.All
open import Implicit.Language.Lookup.All
open import Implicit.Language.Occur.All
open import Implicit.Language.OpenClose.Base
open import Implicit.Language.Regular.All
open import Implicit.Language.Ground.Base

⊢c-≫-⊢r : SRegular Γ
          → Γ ⊢c A
          → Γ ≫ A ⇘ A%
          → Γ ⊢r A%
⊢c-≫-⊢r regΓ ⊢c-int grd-int = ⊢r-int
⊢c-≫-⊢r regΓ (⊢c-var-∙ inΔ) (grd-var= x) = ⊥-elim (∋∙-∋:=-false inΔ x)
⊢c-≫-⊢r regΓ (⊢c-var-∙ inΔ) (grd-var∙ x) = ⊢r-var-∙ inΔ
⊢c-≫-⊢r regΓ (⊢c-var-= inΔ) (grd-var= x) = ∋:=-⊢r regΓ x
⊢c-≫-⊢r regΓ (⊢c-var-= inΔ) (grd-var∙ x) = ⊥-elim (∋∙-∋=-false x inΔ)
⊢c-≫-⊢r regΓ (⊢c-arr cloA cloA₁) (grd-arr grd grd₁) = ⊢r-arr (⊢c-≫-⊢r regΓ cloA grd) (⊢c-≫-⊢r regΓ cloA₁ grd₁)
⊢c-≫-⊢r regΓ (⊢c-∀ cloA) (grd-∀ grd) = ⊢r-∀ (⊢c-≫-⊢r (reg-S∙ regΓ) cloA grd)

⊢r-≫-eq : Γ ⊢r A
        → Γ ≫ A ⇘ A
⊢r-≫-eq ⊢r-int = grd-int
⊢r-≫-eq (⊢r-var-∙ inΓ) = grd-var∙ inΓ
⊢r-≫-eq (⊢r-arr regA regA₁) = grd-arr (⊢r-≫-eq regA) (⊢r-≫-eq regA₁)
⊢r-≫-eq (⊢r-∀ regA) = grd-∀ (⊢r-≫-eq regA)

⊢r-≫-eq' : Γ ⊢r A
         → Γ ≫ A ⇘ A%
         → A ≡ A%
⊢r-≫-eq' ⊢r-int grd-int = refl
⊢r-≫-eq' (⊢r-var-∙ inΓ) (grd-var= x) = ⊥-elim (∋∙-∋:=-false inΓ x)
⊢r-≫-eq' (⊢r-var-∙ inΓ) (grd-var∙ x) = refl
⊢r-≫-eq' (⊢r-arr regA regA₁) (grd-arr grd grd₁) = cong₂ _`→_ (⊢r-≫-eq' regA grd) (⊢r-≫-eq' regA₁ grd₁)
⊢r-≫-eq' (⊢r-∀ regA) (grd-∀ grd) = cong `∀_ (⊢r-≫-eq' regA grd)

⊢c-≫-⊢c : SRegular Γ
          → Γ ⊢c A
          → Γ ≫ A ⇘ A%
          → Γ ⊢c A%
⊢c-≫-⊢c regΓ cloA grd = ⊢r-⊢c (⊢c-≫-⊢r regΓ cloA grd)
