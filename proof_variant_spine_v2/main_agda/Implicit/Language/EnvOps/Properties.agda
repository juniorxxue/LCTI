module Implicit.Language.EnvOps.Properties where

open import Implicit.Language.Base
open import Implicit.Language.Shift.All
open import Implicit.Language.Lookup.All
open import Implicit.Language.EnvOps.Base

----------------------------------------------------------------------
--+                     replacement properties                     +--
----------------------------------------------------------------------

inst-affect-one : [ A / X ] Γ ⟹ Δ
                → Γ ∋^ k
                → Δ ∋= k
                → k ≡ X
inst-affect-one (⟹^0 cloA env up) Z inΔ = refl
inst-affect-one (⟹^0 cloA env up) (S^ inΓ) (S= inΔ) = ⊥-elim (∋^-∋=-false inΓ inΔ)
inst-affect-one (⟹^S inst up1) (S^ inΓ) (S^ inΔ) = cong #S (inst-affect-one inst inΓ inΔ)
inst-affect-one (⟹∙S inst up1) (S∙ inΓ) (S∙ inΔ) = cong #S (inst-affect-one inst inΓ inΔ)
inst-affect-one (⟹,S inst) (S, inΓ) (S, inΔ) = inst-affect-one inst inΓ inΔ
inst-affect-one (⟹=S inst up1) (S= inΓ) (S= inΔ) = cong #S (inst-affect-one inst inΓ inΔ)
