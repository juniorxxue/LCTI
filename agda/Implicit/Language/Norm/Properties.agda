module Implicit.Language.Norm.Properties where

open import Implicit.Language.Base
open import Implicit.Language.Shift.All
open import Implicit.Language.Lookup.All
open import Implicit.Language.Norm.Base


postulate
  ⊢n-weaken,0 : Γ ⊢n A
              → Γ ⊢n T
              → Γ , T ⊢n A

  ⊢n-weaken∙0 : Γ ⊢n A
              → ↑ty0 A ⇘ A'
              → Γ ,∙ ⊢n A'

  ⊢n-weaken^0 : Γ ⊢n A
              → ↑ty0 A ⇘ A'
              → Γ ,^ ⊢n A'

  ⊢n-weaken=0 : Γ ⊢n A
              → ↑ty0 A ⇘ A'
              → Γ ⊢n T
              → Γ ,= T ⊢n A'


∋:=-norm : Norm Γ
         → Γ ∋ X := A
         → Γ ⊢n A
∋:=-norm (nom-S, nΓ nrmA) (S, inΓ) = ⊢n-weaken,0 (∋:=-norm nΓ inΓ) nrmA
∋:=-norm (nom-S∙ nΓ) (S∙ inΓ up) = ⊢n-weaken∙0 (∋:=-norm nΓ inΓ) up
∋:=-norm (nom-S^ nΓ) (S^ inΓ up) = ⊢n-weaken^0 (∋:=-norm nΓ inΓ) up
∋:=-norm (nom-S= nΓ nomA) (Z up) = ⊢n-weaken=0 nomA up nomA
∋:=-norm (nom-S= nΓ nomA) (S= inΓ up) = ⊢n-weaken=0 (∋:=-norm nΓ inΓ) up nomA
