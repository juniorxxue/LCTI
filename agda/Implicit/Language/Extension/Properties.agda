module Implicit.Language.Extension.Properties where

open import Implicit.Language.Base
open import Implicit.Language.Lookup.All

open import Implicit.Language.EnvOps.Base
open import Implicit.Language.Regular.Base

open import Implicit.Language.Extension.Base

⊆-refl : SRegular Γ
       → Γ ⊆ Γ
⊆-refl (reg-Z regΓ) = mark regΓ
⊆-refl (reg-S∙ senv) = uvar (⊆-refl senv)
⊆-refl (reg-S^ senv) = evar (⊆-refl senv)
⊆-refl (reg-S= senv regA) = svar (⊆-refl senv) regA

⊆-∋∙ : Γ ∋∙ X
     → Γ ⊆ Δ
     → Δ ∋∙ X
⊆-∋∙ Z (uvar ext) = Z
⊆-∋∙ (S∙ inΓ) (uvar ext) = S∙ (⊆-∋∙ inΓ ext)
⊆-∋∙ (S= inΓ) (svar ext regA) = S= (⊆-∋∙ inΓ ext)
⊆-∋∙ (S^ inΓ) (evar ext) = S^ (⊆-∋∙ inΓ ext)
⊆-∋∙ (S^ inΓ) (evar-sol ext regA) = S= (⊆-∋∙ inΓ ext)
⊆-∋∙ (S⋈ inΓ) (mark x) = S⋈ inΓ

⊆-∋∙' : Δ ∋∙ X
      → Γ ⊆ Δ
      → Γ ∋∙ X
⊆-∋∙' Z (uvar ext) = Z
⊆-∋∙' (S∙ inΔ) (uvar ext) = S∙ (⊆-∋∙' inΔ ext)
⊆-∋∙' (S= inΔ) (evar-sol ext regA) = S^ (⊆-∋∙' inΔ ext)
⊆-∋∙' (S= inΔ) (svar ext regA) = S= (⊆-∋∙' inΔ ext)
⊆-∋∙' (S^ inΔ) (evar ext) = S^ (⊆-∋∙' inΔ ext)
⊆-∋∙' (S⋈ inΔ) (mark x) = S⋈ inΔ

⊆-⊢r : Γ ⊢r A
     → Γ ⊆ Δ
     → Δ ⊢r A
⊆-⊢r ⊢r-int ext = ⊢r-int
⊆-⊢r (⊢r-var-∙ inΓ) ext = ⊢r-var-∙ (⊆-∋∙ inΓ ext)
⊆-⊢r (⊢r-arr regA regA₁) ext = ⊢r-arr (⊆-⊢r regA ext) (⊆-⊢r regA₁ ext)
⊆-⊢r (⊢r-∀ regA) ext = ⊢r-∀ (⊆-⊢r regA (uvar ext))

⊆-⊢r' : Δ ⊢r A
      → Γ ⊆ Δ
      → Γ ⊢r A
⊆-⊢r' ⊢r-int ext = ⊢r-int
⊆-⊢r' (⊢r-var-∙ inΓ) ext = ⊢r-var-∙ (⊆-∋∙' inΓ ext)
⊆-⊢r' (⊢r-arr regA regA₁) ext = ⊢r-arr (⊆-⊢r' regA ext) (⊆-⊢r' regA₁ ext)
⊆-⊢r' (⊢r-∀ regA) ext = ⊢r-∀ (⊆-⊢r' regA (uvar ext))

⊆-trans : Γ ⊆ Ω
        → Ω ⊆ Δ
        → Γ ⊆ Δ
⊆-trans (uvar ext1) (uvar ext2) = uvar (⊆-trans ext1 ext2)
⊆-trans (evar ext1) (evar ext2) = evar (⊆-trans ext1 ext2)
⊆-trans (evar ext1) (evar-sol ext2 regA) = evar-sol (⊆-trans ext1 ext2) regA
⊆-trans (evar-sol ext1 regA) (svar ext2 regA₁) = evar-sol (⊆-trans ext1 ext2) (⊆-⊢r regA ext2)
⊆-trans (svar ext1 regA) (svar ext2 regA₁) = svar (⊆-trans ext1 ext2) regA
⊆-trans (mark x) ext2 = ext2


⊆-antisymm : Γ ⊆ Δ
           → Δ ⊆ Γ
           → Γ ≡ Δ
⊆-antisymm (uvar ext1) (uvar ext2) with refl ← ⊆-antisymm ext1 ext2 = refl
⊆-antisymm (evar ext1) (evar ext2) with refl ← ⊆-antisymm ext1 ext2 = refl
⊆-antisymm (svar ext1 regA) (svar ext2 regA₁) with refl ← ⊆-antisymm ext1 ext2 = refl
⊆-antisymm (mark x) (mark x₁) = refl
