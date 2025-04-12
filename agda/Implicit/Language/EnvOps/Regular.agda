module Implicit.Language.EnvOps.Regular where

-- some properties about regular, but put here for avoiding dependency

open import Implicit.Language.Base
open import Implicit.Language.Shift.All
open import Implicit.Language.Subst.All
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


∋∙-strengthen=' : Γ ∋∙ X
                → Γ ◀ k ∙⇘ Γ'
                → (¬p : k ≢ X)
                → Γ' ∋∙ punchOut ¬p
∋∙-strengthen=' Z ◀Z ¬p = ⊥-elim (¬p refl)
∋∙-strengthen=' Z (◀S∙ new) ¬p = Z
∋∙-strengthen=' (S, inΓ) (◀S, new x) ¬p = S, (∋∙-strengthen=' inΓ new ¬p)
∋∙-strengthen=' (S∙ inΓ) ◀Z ¬p = inΓ
∋∙-strengthen=' (S∙ inΓ) (◀S∙ new) ¬p = S∙ (∋∙-strengthen=' inΓ new (λ x → ¬p (cong #S x)))
∋∙-strengthen=' (S= inΓ) (◀S= new x) ¬p = S= (∋∙-strengthen=' inΓ new (λ x₁ → ¬p (cong #S x₁)))
∋∙-strengthen=' (S^ inΓ) (◀S^ new) ¬p = S^ (∋∙-strengthen=' inΓ new (λ x → ¬p (cong #S x)))
∋∙-strengthen=' (S⋈ inΓ) (◀S⋈ new) ¬p = S⋈ (∋∙-strengthen=' inΓ new ¬p)


stx-⊢r : Γ ∋∙ X
       → Γ ◀ k ∙⇘ Γ'
       → Γ' ⊢r A
       → ⟦ k / A ⟧ˣ X ⇘ B*
       → Γ' ⊢r B*
stx-⊢r inΓ new regA stx-eq = regA
stx-⊢r inΓ new regA (stx-neq ¬p) = ⊢r-var-∙ (∋∙-strengthen=' inΓ new ¬p)

st-⊢r : Γ ⊢r B
      → Γ ◀ k ∙⇘ Γ'
      → Γ' ⊢r A
      → ⟦ k / A ⟧ B ⇘ B*
      → Γ' ⊢r B*
st-⊢r ⊢r-int newΓ regA st-int = ⊢r-int
st-⊢r (⊢r-var-∙ inΓ) newΓ regA (st-var stx) = stx-⊢r inΓ newΓ regA stx
st-⊢r (⊢r-arr upB upB₁) newΓ regA (st-arr stB stB₁) = ⊢r-arr (st-⊢r upB newΓ regA stB) (st-⊢r upB₁ newΓ regA stB₁)
st-⊢r (⊢r-∀ upB) newΓ regA (st-∀ up stB) = ⊢r-∀ (st-⊢r upB (◀S∙ newΓ) (⊢r-weaken∙0 regA up) stB)

st0-⊢r : Γ ⊢r `∀ B
       → Γ ⊢r A
       → ⟦ A ⟧ B ⇘ B*
       → Γ ⊢r B*
st0-⊢r (⊢r-∀ reg) regA st = st-⊢r reg ◀Z regA st


