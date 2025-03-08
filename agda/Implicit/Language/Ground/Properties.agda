module Implicit.Language.Ground.Properties where

open import Implicit.Language.Base
open import Implicit.Language.Shift.All
open import Implicit.Language.Lookup.All
open import Implicit.Language.Occur.All
open import Implicit.Language.OpenClose.Base
open import Implicit.Language.Regular.All
open import Implicit.Language.Ground.Base
open import Implicit.Language.Extension.All

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


⊆-⊢c-≫ : Γ ⊆ Δ
       → Γ ⊢c A
       → Δ ≫ A ⇘ A%
       → Γ ≫ A ⇘ A%
⊆-⊢c-≫ ext ⊢c-int grd-int = grd-int
⊆-⊢c-≫ ext (⊢c-var-∙ inΔ) (grd-var= x) = ⊥-elim (∋∙-∋:=-false (⊆-∋∙ inΔ ext) x)
⊆-⊢c-≫ ext (⊢c-var-∙ inΔ) (grd-var∙ x) = grd-var∙ inΔ
⊆-⊢c-≫ ext (⊢c-var-= inΔ) (grd-var= x) = grd-var= (helper x ext inΔ)
  where helper : Δ ∋ X := A%
               → Γ ⊆ Δ
               → Γ ∋= X
               → Γ ∋ X := A%
        helper (Z up) (svar ext regA) Z = Z up
        helper (S∙ inΔ up) (uvar ext) (S∙ inΓ) = S∙ (helper inΔ ext inΓ) up
        helper (S^ inΔ up) (evar ext) (S^ inΓ) = S^ (helper inΔ ext inΓ) up
        helper (S= inΔ up) (evar-sol ext regA) (S^ inΓ) = S^ (helper inΔ ext inΓ) up
        helper (S= inΔ up) (svar ext regA) (S= inΓ) = S= (helper inΔ ext inΓ) up
⊆-⊢c-≫ ext (⊢c-var-= inΔ) (grd-var∙ x) = ⊥-elim (∋∙-∋=-false (⊆-∋∙' x ext) inΔ)
⊆-⊢c-≫ ext (⊢c-arr cloA cloA₁) (grd-arr grd grd₁) = grd-arr (⊆-⊢c-≫ ext cloA grd) (⊆-⊢c-≫ ext cloA₁ grd₁)
⊆-⊢c-≫ ext (⊢c-∀ cloA) (grd-∀ grd) = grd-∀ (⊆-⊢c-≫ (uvar ext) cloA grd)
