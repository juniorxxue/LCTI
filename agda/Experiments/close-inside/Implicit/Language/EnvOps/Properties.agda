module Implicit.Language.EnvOps.Properties where

open import Implicit.Language.Base
open import Implicit.Language.Shift
open import Implicit.Language.Lookup
open import Implicit.Language.EnvOps.Base

inst-in : [ A / k ] Γ ⟹ Γ' ↪ B
        → Γ' ∋ k := B
inst-in (⟹^0 up) = Z up
inst-in (⟹^S inst up1 up2) = S^ (inst-in inst) up2
inst-in (⟹∙S inst up1 up2) = S∙ (inst-in inst) up2
inst-in (⟹,S inst) = S, (inst-in inst)
inst-in (⟹=S inst up1 up2) = S= (inst-in inst) up2
