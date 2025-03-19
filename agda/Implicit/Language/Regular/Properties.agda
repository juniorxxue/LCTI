module Implicit.Language.Regular.Properties where

open import Implicit.Language.Base
open import Implicit.Language.Shift.All
open import Implicit.Language.Lookup.All
open import Implicit.Language.OpenClose.Base
open import Implicit.Language.Regular.Base


postulate
  ⊢r-weaken,0 : Γ ⊢r A
              → Γ ⊢r T
              → Γ , T ⊢r A

  ⊢r-weaken∙0 : Γ ⊢r A
              → ↑ty0 A ⇘ A'
              → Γ ,∙ ⊢r A'

  ⊢r-weaken^0 : Γ ⊢r A
              → ↑ty0 A ⇘ A'
              → Γ ,^ ⊢r A'

  ⊢r-weaken=0 : Γ ⊢r A
              → ↑ty0 A ⇘ A'
              → Γ ⊢r T
              → Γ ,= T ⊢r A'

  ⊢r-weaken⋈0 : Γ ⊢r A
              → Γ ⋈ ⊢r A


  ⊢r-strengthen,0 : Γ , A ⊢r B
                  → Γ ⊢r B

  ⊢r-strengthen^0 : Γ ,^ ⊢r A'
                  → ↑ty0 A ⇘ A'
                  → Γ ⊢r A

  ⊢r-strengthen⋈0 : Γ ⋈ ⊢r A
                 → Γ ⊢r A

  ⊢r-strengthen∙0 : Γ ,∙ ⊢r A'
                  → ↑ty0 A ⇘ A'
                  → Γ ⊢r A


∋:=-⊢r : SRegular Γ
         → Γ ∋ X := A
         → Γ ⊢r A
∋:=-⊢r (reg-S= senv regA) (Z up) = ⊢r-weaken=0 regA up regA
∋:=-⊢r (reg-S∙ senv) (S∙ inΓ up) = ⊢r-weaken∙0 (∋:=-⊢r senv inΓ) up
∋:=-⊢r (reg-S^ senv) (S^ inΓ up) = ⊢r-weaken^0 (∋:=-⊢r senv inΓ) up
∋:=-⊢r (reg-S= senv regA) (S= inΓ up) = ⊢r-weaken=0 (∋:=-⊢r senv inΓ) up regA

∋⦂-⊢r : TRegular Γ
      → Γ ∋ x ⦂ A
      → Γ ⊢r A
∋⦂-⊢r (reg-S, regΓ regA) Z = ⊢r-weaken,0 regA regA
∋⦂-⊢r (reg-S, regΓ regA) (S, inΓ) = ⊢r-weaken,0 (∋⦂-⊢r regΓ inΓ) regA
∋⦂-⊢r (reg-S∙ regΓ) (S∙ inΓ up) = ⊢r-weaken∙0 (∋⦂-⊢r regΓ inΓ) up
∋⦂-⊢r (reg-S^ regΓ) (S^ inΓ up) = ⊢r-weaken^0 (∋⦂-⊢r regΓ inΓ) up
∋⦂-⊢r (reg-S= regΓ regA) (S= inΓ up) = ⊢r-weaken=0 (∋⦂-⊢r regΓ inΓ) up regA


∋∙-𝕣 : 𝕣 Γ ∋∙ X
     → Γ ∋∙ X
∋∙-𝕣 {Γ = Γ , A} (S, inΓ) = S, (∋∙-𝕣 inΓ)
∋∙-𝕣 {Γ = Γ ,^} (S^ inΓ) = S^ (∋∙-𝕣 inΓ)
∋∙-𝕣 {Γ = Γ ,∙} Z = Z
∋∙-𝕣 {Γ = Γ ,∙} (S∙ inΓ) = S∙ (∋∙-𝕣 inΓ)
∋∙-𝕣 {Γ = Γ ,= A} (S= inΓ) = S= (∋∙-𝕣 inΓ)
∋∙-𝕣 {Γ = Γ ⋈} inΓ = S⋈ inΓ

∋∙-𝕣' : Γ ∋∙ X
     → 𝕣 Γ ∋∙ X
∋∙-𝕣' Z = Z
∋∙-𝕣' (S, inΓ) = S, (∋∙-𝕣' inΓ)
∋∙-𝕣' (S∙ inΓ) = S∙ (∋∙-𝕣' inΓ)
∋∙-𝕣' (S= inΓ) = S= (∋∙-𝕣' inΓ)
∋∙-𝕣' (S^ inΓ) = S^ (∋∙-𝕣' inΓ)
∋∙-𝕣' (S⋈ inΓ) = inΓ

⊢r-𝕣 : 𝕣 Γ ⊢r A
     → Γ ⊢r A
⊢r-𝕣 ⊢r-int = ⊢r-int
⊢r-𝕣 (⊢r-var-∙ inΓ) = ⊢r-var-∙ (∋∙-𝕣 inΓ)
⊢r-𝕣 (⊢r-arr regA regA₁) = ⊢r-arr (⊢r-𝕣 regA) (⊢r-𝕣 regA₁)
⊢r-𝕣 (⊢r-∀ regA) = ⊢r-∀ (⊢r-𝕣 regA)

⊢r-𝕣' : Γ ⊢r A
      → 𝕣 Γ ⊢r A
⊢r-𝕣' ⊢r-int = ⊢r-int
⊢r-𝕣' (⊢r-var-∙ inΓ) = ⊢r-var-∙ (∋∙-𝕣' inΓ)
⊢r-𝕣' (⊢r-arr regA regA₁) = ⊢r-arr (⊢r-𝕣' regA) (⊢r-𝕣' regA₁)
⊢r-𝕣' (⊢r-∀ regA) = ⊢r-∀ (⊢r-𝕣' regA)

⊢r-⊢c : Γ ⊢r A
      → Γ ⊢c A
⊢r-⊢c ⊢r-int = ⊢c-int
⊢r-⊢c (⊢r-var-∙ inΓ) = ⊢c-var-∙ inΓ
⊢r-⊢c (⊢r-arr regA regA₁) = ⊢c-arr (⊢r-⊢c regA) (⊢r-⊢c regA₁)
⊢r-⊢c (⊢r-∀ regA) = ⊢c-∀ (⊢r-⊢c regA)
