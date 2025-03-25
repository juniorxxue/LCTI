module Implicit.Language.EnvOps.Regular where

-- some properties about regular, but put here for avoiding dependency

open import Implicit.Language.Base
open import Implicit.Language.Shift.All
open import Implicit.Language.Lookup.All
open import Implicit.Language.Regular.All

open import Implicit.Language.EnvOps.Base
open import Implicit.Language.EnvOps.Inst
open import Implicit.Language.EnvOps.InsertTVar
open import Implicit.Language.EnvOps.InsertEVar
open import Implicit.Language.EnvOps.InsertUVar
open import Implicit.Language.EnvOps.InsertSVar
open import Implicit.Language.EnvOps.RemoveEVar
open import Implicit.Language.EnvOps.RemoveUVar

⊢r-strengthen∙0 : Γ ,∙ ⊢r A'
                  → ↑ty0 A ⇘ A'
                  → Γ ⊢r A
⊢r-strengthen∙0 regA upA = ⊢r-strengthen∙ regA ◀Z upA


⊢r-strengthen^0 : Γ ,^ ⊢r A'
                  → ↑ty0 A ⇘ A'
                  → Γ ⊢r A
⊢r-strengthen^0 regA upA = ⊢r-strengthen^ regA ◀Z upA

⊢r-weaken=0 : Γ ⊢r A
              → ↑ty0 A ⇘ A'
              → Γ ⊢r T
              → Γ ,= T ⊢r A'
⊢r-weaken=0 regA upA regT = ⊢r-weaken= regA (▶Z regT) upA


⊢r-weaken∙0 : Γ ⊢r A
              → ↑ty0 A ⇘ A'
              → Γ ,∙ ⊢r A'
⊢r-weaken∙0 regA upA = ⊢r-weaken∙ regA ▶Z upA

⊢r-weaken⋈0 : Γ ⊢r A
            → Γ ⋈ ⊢r A
⊢r-weaken⋈0 regA = ⊢r-𝕣 regA

⊢r-weaken,0 : Γ ⊢r A
             → Γ ⊢r T
             → Γ , T ⊢r A
⊢r-weaken,0 regA regT = ⊢r-weaken, regA (▶Z regT)

⊢r-weaken^0 : Γ ⊢r A
             → ↑ty0 A ⇘ A'
             → Γ ,^ ⊢r A'
⊢r-weaken^0 regA up = ⊢r-weaken^ regA ▶Z up


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

inst-⊢r : [ A / k ] Γ ⟹ Δ
        → Γ ⊢r A
inst-⊢r (⟹^0 up regA env) = ⊢r-weaken^0 regA up
inst-⊢r (⟹^S inst up1) = ⊢r-weaken^0 (inst-⊢r inst) up1
inst-⊢r (⟹∙S inst up1) = ⊢r-weaken∙0 (inst-⊢r inst) up1
inst-⊢r (⟹=S inst up1 regB) = ⊢r-weaken=0 (inst-⊢r inst) up1 regB
