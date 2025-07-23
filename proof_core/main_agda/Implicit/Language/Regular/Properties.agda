module Implicit.Language.Regular.Properties where

open import Implicit.Language.Base
open import Implicit.Language.Shift.All
open import Implicit.Language.Lookup.All
open import Implicit.Language.OpenClose.Base
open import Implicit.Language.Regular.Base

abstract
  ∋∙-𝕣 : Γ ∋∙ X
       → Δ ↳ Γ
       → Γ ∋∙ X
  ∋∙-𝕣 (S, inΓ) (↳S, tf) = S, inΓ
  ∋∙-𝕣 (S^ inΓ) (↳S^ tf) = S^ inΓ
  ∋∙-𝕣 Z (↳S∙ tf) = Z
  ∋∙-𝕣 (S∙ inΓ) (↳S∙ tf) = S∙ inΓ
  ∋∙-𝕣 (S= inΓ) (↳S= tf) = S= inΓ
  ∋∙-𝕣 inΓ ↳⋈ = inΓ

  ∋∙-𝕣' : Δ ∋∙ X
        → Δ ↳ Γ
        → Γ ∋∙ X
  ∋∙-𝕣' (S, inΓ) (↳S, tf) = S, (∋∙-𝕣' inΓ tf)
  ∋∙-𝕣' (S^ inΓ) (↳S^ tf) = S^ (∋∙-𝕣' inΓ tf)
  ∋∙-𝕣' Z (↳S∙ tf) = Z
  ∋∙-𝕣' (S∙ inΓ) (↳S∙ tf) = S∙ (∋∙-𝕣' inΓ tf)
  ∋∙-𝕣' (S= inΓ) (↳S= tf) = S= (∋∙-𝕣' inΓ tf)
  ∋∙-𝕣' (S⋈ inΓ) ↳⋈ = inΓ


  ⊢r-⊢c : Γ ⊢r A
        → Γ ⊢c A
  ⊢r-⊢c ⊢r-int = ⊢c-int
  ⊢r-⊢c (⊢r-var-∙ inΓ) = ⊢c-var-∙ inΓ
  ⊢r-⊢c (⊢r-arr regA regA₁) = ⊢c-arr (⊢r-⊢c regA) (⊢r-⊢c regA₁)
  ⊢r-⊢c (⊢r-∀ regA) = ⊢c-∀ (⊢r-⊢c regA)

postulate
  ⊢r-𝕣 : Γ ⊢r A
       → Δ ↳ Γ
       → Δ ⊢r A

  ⊢r-𝕣' : Δ ⊢r A
        → Δ ↳ Γ
        → Γ ⊢r A
