module Implicit.Language.Extension.Preservation where

open import Implicit.Language.Base
open import Implicit.Language.Lookup.All
open import Implicit.Language.EnvOps.Base
open import Implicit.Language.Regular.Base
open import Implicit.Language.Extension.Base
open import Implicit.Language.OpenClose.Base


⊆-∋∙ : Γ ∋∙ X
     → Γ ⊆ Δ
     → Δ ∋∙ X
⊆-∋∙ Z (uvar ext) = Z
⊆-∋∙ (S∙ inΓ) (uvar ext) = S∙ (⊆-∋∙ inΓ ext)
⊆-∋∙ (S= inΓ) (svar ext regA) = S= (⊆-∋∙ inΓ ext)
⊆-∋∙ (S^ inΓ) (evar ext) = S^ (⊆-∋∙ inΓ ext)
⊆-∋∙ (S^ inΓ) (evar-sol ext regA) = S= (⊆-∋∙ inΓ ext)
⊆-∋∙ (S⋈ inΓ) (mark x) = S⋈ (⊆-∋∙ inΓ x)
⊆-∋∙ (S, inΓ) (tvar ext regA) = S, (⊆-∋∙ inΓ ext)

⊆-∋:= : Γ ∋ X := A
      → Γ ⊆ Δ
      → Δ ∋ X := A
⊆-∋:= (Z up) (svar ext regA) = Z up
⊆-∋:= (S∙ inΓ up) (uvar ext) = S∙ (⊆-∋:= inΓ ext) up
⊆-∋:= (S^ inΓ up) (evar ext) = S^ (⊆-∋:= inΓ ext) up
⊆-∋:= (S^ inΓ up) (evar-sol ext regA) = S= (⊆-∋:= inΓ ext) up
⊆-∋:= (S= inΓ up) (svar ext regA) = S= (⊆-∋:= inΓ ext) up
⊆-∋:= (S, inΓ) (tvar ext regA) = S, (⊆-∋:= inΓ ext)
⊆-∋:= (S⋈ inΓ) (mark ext) = S⋈ (⊆-∋:= inΓ ext)

⊆-∋= : Γ ∋= X
     → Γ ⊆ Δ
     → Δ ∋= X
⊆-∋= Z (svar ext regA) = Z
⊆-∋= (S∙ inΓ) (uvar ext) = S∙ (⊆-∋= inΓ ext)
⊆-∋= (S^ inΓ) (evar ext) = S^ (⊆-∋= inΓ ext)
⊆-∋= (S^ inΓ) (evar-sol ext regA) = S= (⊆-∋= inΓ ext)
⊆-∋= (S= inΓ) (svar ext regA) = S= (⊆-∋= inΓ ext)
⊆-∋= (S, inΓ) (tvar ext regA) = S, (⊆-∋= inΓ ext)
⊆-∋= (S⋈ inΓ) (mark ext) = S⋈ (⊆-∋= inΓ ext)

⊆-∋∙' : Δ ∋∙ X
      → Γ ⊆ Δ
      → Γ ∋∙ X
⊆-∋∙' Z (uvar ext) = Z
⊆-∋∙' (S∙ inΔ) (uvar ext) = S∙ (⊆-∋∙' inΔ ext)
⊆-∋∙' (S= inΔ) (evar-sol ext regA) = S^ (⊆-∋∙' inΔ ext)
⊆-∋∙' (S= inΔ) (svar ext regA) = S= (⊆-∋∙' inΔ ext)
⊆-∋∙' (S^ inΔ) (evar ext) = S^ (⊆-∋∙' inΔ ext)
⊆-∋∙' (S, inΔ) (tvar ext regA) = S, (⊆-∋∙' inΔ ext)
⊆-∋∙' (S⋈ inΔ) (mark x) = S⋈ (⊆-∋∙' inΔ x)

⊆-⊢r : Γ ⊢r A
     → Γ ⊆ Δ
     → Δ ⊢r A
⊆-⊢r ⊢r-int ext = ⊢r-int
⊆-⊢r (⊢r-var-∙ inΓ) ext = ⊢r-var-∙ (⊆-∋∙ inΓ ext)
⊆-⊢r (⊢r-arr regA regA₁) ext = ⊢r-arr (⊆-⊢r regA ext) (⊆-⊢r regA₁ ext)
⊆-⊢r (⊢r-∀ regA) ext = ⊢r-∀ (⊆-⊢r regA (uvar ext))

⊆-⊢c : Γ ⊢c A
     → Γ ⊆ Δ
     → Δ ⊢c A
⊆-⊢c ⊢c-int ext = ⊢c-int
⊆-⊢c (⊢c-var-∙ inΔ) ext = ⊢c-var-∙ (⊆-∋∙ inΔ ext)
⊆-⊢c (⊢c-var-= inΔ) ext = ⊢c-var-= (⊆-∋= inΔ ext)
⊆-⊢c (⊢c-arr cloA cloA₁) ext = ⊢c-arr (⊆-⊢c cloA ext) (⊆-⊢c cloA₁ ext)
⊆-⊢c (⊢c-∀ cloA) ext = ⊢c-∀ (⊆-⊢c cloA (uvar ext))

⊆-⊢r' : Δ ⊢r A
      → Γ ⊆ Δ
      → Γ ⊢r A
⊆-⊢r' ⊢r-int ext = ⊢r-int
⊆-⊢r' (⊢r-var-∙ inΓ) ext = ⊢r-var-∙ (⊆-∋∙' inΓ ext)
⊆-⊢r' (⊢r-arr regA regA₁) ext = ⊢r-arr (⊆-⊢r' regA ext) (⊆-⊢r' regA₁ ext)
⊆-⊢r' (⊢r-∀ regA) ext = ⊢r-∀ (⊆-⊢r' regA (uvar ext))

⊆-tregular : TRegular Γ
          → Γ ⊆ Δ
          → TRegular Δ
⊆-tregular reg-Z empty = reg-Z
⊆-tregular (reg-S, regΓ regA) (tvar ext regA₁) = reg-S, (⊆-tregular regΓ ext) (⊆-⊢r regA ext)
⊆-tregular (reg-S∙ regΓ) (uvar ext) = reg-S∙ (⊆-tregular regΓ ext)
⊆-tregular (reg-S^ regΓ) (evar ext) = reg-S^ (⊆-tregular regΓ ext)
⊆-tregular (reg-S^ regΓ) (evar-sol ext regA) = reg-S= (⊆-tregular regΓ ext) regA
⊆-tregular (reg-S= regΓ regA) (svar ext regA₁) = reg-S= (⊆-tregular regΓ ext) (⊆-⊢r regA ext)

⊆-sregular : SRegular Γ
          → Γ ⊆ Δ
          → SRegular Δ
⊆-sregular (reg-Z regΓ) (mark x) = reg-Z (⊆-tregular regΓ x)
⊆-sregular (reg-S∙ regΓ) (uvar ext) = reg-S∙ (⊆-sregular regΓ ext)
⊆-sregular (reg-S^ regΓ) (evar ext) = reg-S^ (⊆-sregular regΓ ext)
⊆-sregular (reg-S^ regΓ) (evar-sol ext regA) = reg-S= (⊆-sregular regΓ ext) regA
⊆-sregular (reg-S= regΓ regA) (svar ext regA₁) = reg-S= (⊆-sregular regΓ ext) (⊆-⊢r regA ext)

⊆-tregular' : TRegular Δ
            → Γ ⊆ Δ
            → TRegular Γ
⊆-tregular' reg-Z empty = reg-Z
⊆-tregular' (reg-S, treg regA) (tvar ext regA₁) = reg-S, (⊆-tregular' treg ext) regA₁
⊆-tregular' (reg-S∙ treg) (uvar ext) = reg-S∙ (⊆-tregular' treg ext)
⊆-tregular' (reg-S^ treg) (evar ext) = reg-S^ (⊆-tregular' treg ext)
⊆-tregular' (reg-S= treg regA) (evar-sol ext regA₁) = reg-S^ (⊆-tregular' treg ext)
⊆-tregular' (reg-S= treg regA) (svar ext regA₁) = reg-S= (⊆-tregular' treg ext) regA₁

⊆-sregular' : SRegular Δ
           → Γ ⊆ Δ
           → SRegular Γ
⊆-sregular' (reg-Z regΓ) (mark x) = reg-Z (⊆-tregular' regΓ x)
⊆-sregular' (reg-S∙ reg) (uvar ext) = reg-S∙ (⊆-sregular' reg ext)
⊆-sregular' (reg-S^ reg) (evar ext) = reg-S^ (⊆-sregular' reg ext)
⊆-sregular' (reg-S= reg regA) (evar-sol ext regA₁) = reg-S^ (⊆-sregular' reg ext)
⊆-sregular' (reg-S= reg regA) (svar ext regA₁) = reg-S= (⊆-sregular' reg ext) regA₁
