module Implicit.Language.EnvOps.Properties where

open import Implicit.Language.Base
open import Implicit.Language.Shift.All
open import Implicit.Language.Lookup.All
open import Implicit.Language.EnvOps.Base

inst-in : [ A / k ] Γ ⟹ Γ'
        → Γ' ∋ k := A
inst-in (⟹^0 up) = Z up
inst-in (⟹^S inst up1) = S^ (inst-in inst) up1
inst-in (⟹∙S inst up1) = S∙ (inst-in inst) up1
inst-in (⟹,S inst) = S, (inst-in inst)
inst-in (⟹=S inst up1) = S= (inst-in inst) up1

----------------------------------------------------------------------
--+                     replacement properties                     +--
----------------------------------------------------------------------

∙⟹-:=-eq : Γ ∋ X := A₁
          → [ B / k ] Γ ∙⟹ Γ'
          → Γ' ∋ X := A₂
          → A₁ ≡ A₂
∙⟹-:=-eq (Z up) (∙⟹=S newΓ up1) (Z up₁) = ↑ty-unique up up₁
∙⟹-:=-eq (S, in1) (∙⟹,S newΓ) (S, in2) = ∙⟹-:=-eq in1 newΓ in2
∙⟹-:=-eq (S∙ in1 up) (∙⟹^0 up₁) (S= in2 up₂) with ∋:=-unique in1 in2
... | refl = ↑ty-unique up up₂
∙⟹-:=-eq (S∙ in1 up) (∙⟹∙S newΓ up1) (S∙ in2 up₁) with ∙⟹-:=-eq in1 newΓ in2
... | refl = ↑ty-unique up up₁
∙⟹-:=-eq (S^ in1 up) (∙⟹^S newΓ up1) (S^ in2 up₁) with ∙⟹-:=-eq in1 newΓ in2
... | refl = ↑ty-unique up up₁
∙⟹-:=-eq (S= in1 up) (∙⟹=S newΓ up1) (S= in2 up₁) with ∙⟹-:=-eq in1 newΓ in2
... | refl = ↑ty-unique up up₁

∙⟹-:=-∙-false : Γ ∋ X := A
               → [ B / k ] Γ ∙⟹ Γ'
               → Γ' ∋∙ X
               → ⊥
∙⟹-:=-∙-false (Z up) (∙⟹=S newΓ' up1) ()
∙⟹-:=-∙-false (S, inΓ) (∙⟹,S newΓ') (S, inΓ') = ∙⟹-:=-∙-false inΓ newΓ' inΓ'
∙⟹-:=-∙-false (S∙ inΓ up) (∙⟹^0 up₁) (S= inΓ') = ∋∙-∋:=-false inΓ' inΓ
∙⟹-:=-∙-false (S∙ inΓ up) (∙⟹∙S newΓ' up1) (S∙ inΓ') = ∙⟹-:=-∙-false inΓ newΓ' inΓ'
∙⟹-:=-∙-false (S^ inΓ up) (∙⟹^S newΓ' up1) (S^ inΓ') = ∙⟹-:=-∙-false inΓ newΓ' inΓ'
∙⟹-:=-∙-false (S= inΓ up) (∙⟹=S newΓ' up1) (S= inΓ') = ∙⟹-:=-∙-false inΓ newΓ' inΓ'

∙⟹-∙-:=-eq : Γ ∋∙ k
            → [ B / k ] Γ ∙⟹ Γ'
            → Γ' ∋ k := A
            → A ≡ B
∙⟹-∙-:=-eq Z (∙⟹^0 up) (Z up₁) = ↑ty-unique up₁ up
∙⟹-∙-:=-eq (S, inΓ) (∙⟹,S newΓ) (S, inΓ') = ∙⟹-∙-:=-eq inΓ newΓ inΓ'
∙⟹-∙-:=-eq (S∙ inΓ) (∙⟹∙S newΓ up1) (S∙ inΓ' up) with ∙⟹-∙-:=-eq inΓ newΓ inΓ'
... | refl = ↑ty-unique up up1
∙⟹-∙-:=-eq (S= inΓ) (∙⟹=S newΓ up1) (S= inΓ' up) with ∙⟹-∙-:=-eq inΓ newΓ inΓ'
... | refl = ↑ty-unique up up1
∙⟹-∙-:=-eq (S^ inΓ) (∙⟹^S newΓ up1) (S^ inΓ' up) with ∙⟹-∙-:=-eq inΓ newΓ inΓ'
... | refl = ↑ty-unique up up1

∙⟹-∙-:=-neq-false : Γ ∋∙ X
                   → [ B / k ] Γ ∙⟹ Γ'
                   → Γ' ∋ X := A
                   → k ≢ X
                   → ⊥
∙⟹-∙-:=-neq-false Z (∙⟹^0 up) inΓ' neq = neq refl
∙⟹-∙-:=-neq-false (S, inΓ) (∙⟹,S newΓ) (S, inΓ') neq = ∙⟹-∙-:=-neq-false inΓ newΓ inΓ' neq
∙⟹-∙-:=-neq-false (S∙ inΓ) (∙⟹^0 up) (S= inΓ' up₁) neq = ∋∙-∋:=-false inΓ inΓ'
∙⟹-∙-:=-neq-false (S∙ inΓ) (∙⟹∙S newΓ up1) (S∙ inΓ' up) neq = ∙⟹-∙-:=-neq-false inΓ newΓ inΓ' (≢-pred neq)
∙⟹-∙-:=-neq-false (S= inΓ) (∙⟹=S newΓ up1) (S= inΓ' up) neq = ∙⟹-∙-:=-neq-false inΓ newΓ inΓ' (≢-pred neq)
∙⟹-∙-:=-neq-false (S^ inΓ) (∙⟹^S newΓ up1) (S^ inΓ' up) neq = ∙⟹-∙-:=-neq-false inΓ newΓ inΓ' (≢-pred neq)

∙⟹-∙-eq-false : Γ ∋∙ k
               → [ A / k ] Γ ∙⟹ Γ'
               → Γ' ∋∙ k
               → ⊥
∙⟹-∙-eq-false Z (∙⟹^0 up) ()
∙⟹-∙-eq-false (S, inΓ) (∙⟹,S newΓ) (S, inΓ') = ∙⟹-∙-eq-false inΓ newΓ inΓ'
∙⟹-∙-eq-false (S∙ inΓ) (∙⟹∙S newΓ up1) (S∙ inΓ') = ∙⟹-∙-eq-false inΓ newΓ inΓ'
∙⟹-∙-eq-false (S= inΓ) (∙⟹=S newΓ up1) (S= inΓ') = ∙⟹-∙-eq-false inΓ newΓ inΓ'
∙⟹-∙-eq-false (S^ inΓ) (∙⟹^S newΓ up1) (S^ inΓ') = ∙⟹-∙-eq-false inΓ newΓ inΓ'


inst-affect-one : [ A / X ] Γ ⟹ Δ
                → Γ ∋^ k
                → Δ ∋= k
                → k ≡ X
inst-affect-one (⟹^0 up) Z inΔ = refl
inst-affect-one (⟹^0 up) (S^ inΓ) (S= inΔ) = ⊥-elim (∋^-∋=-false inΓ inΔ)
inst-affect-one (⟹^S inst up1) (S^ inΓ) (S^ inΔ) = cong #S (inst-affect-one inst inΓ inΔ)
inst-affect-one (⟹∙S inst up1) (S∙ inΓ) (S∙ inΔ) = cong #S (inst-affect-one inst inΓ inΔ)
inst-affect-one (⟹,S inst) (S, inΓ) (S, inΔ) = inst-affect-one inst inΓ inΔ
inst-affect-one (⟹=S inst up1) (S= inΓ) (S= inΔ) = cong #S (inst-affect-one inst inΓ inΔ)
