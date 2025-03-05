module Implicit.Language.Regular.Properties where

open import Implicit.Language.Base
open import Implicit.Language.Shift.All
open import Implicit.Language.Lookup.All
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

∋:=-norm : SRegular Γ
         → Γ ∋ X := A
         → Γ ⊢r A
∋:=-norm (reg-S= senv regA) (Z x up) = ⊢r-weaken=0 regA up regA
∋:=-norm (reg-S∙ senv) (S∙ inΓ up) = ⊢r-weaken∙0 (∋:=-norm senv inΓ) up
∋:=-norm (reg-S^ senv) (S^ inΓ up) = ⊢r-weaken^0 (∋:=-norm senv inΓ) up
∋:=-norm (reg-S= senv regA) (S= inΓ up) = ⊢r-weaken=0 (∋:=-norm senv inΓ) up regA
