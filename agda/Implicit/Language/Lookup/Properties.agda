module Implicit.Language.Lookup.Properties where

open import Implicit.Language.Base
open import Implicit.Language.Lookup.Base
open import Implicit.Language.Shift

private variable
  Γ Γ' : Env n m
  k : Fin m
  x : Fin n
  A B : Type m
  

postulate

  -- remove a term binding from the environment
  -- the solution is expected to hold, with the same type
  ∋,-weaken-sol :
      (Γ /,/ k) ∋ x := A
    → Γ ∋ x := A


∋⦂-unique : Γ ∋ x ⦂ A
          → Γ ∋ x ⦂ B
          → A ≡ B
∋⦂-unique Z Z = refl
∋⦂-unique (S, in1) (S, in2) = ∋⦂-unique in1 in2
∋⦂-unique (S∙ in1 x) (S∙ in2 x₁) rewrite ∋⦂-unique in1 in2 = ↑ty-unique x x₁
∋⦂-unique (S^ in1 x) (S^ in2 up) rewrite ∋⦂-unique in1 in2 = ↑ty-unique x up
∋⦂-unique (S= in1 x) (S= in2 x₁) rewrite ∋⦂-unique in1 in2 = ↑ty-unique x x₁


inst-in : [ A / k ] Γ ⟹ Γ' ↪ B
        → Γ' ∋ k := B
inst-in (⟹^0 up) = Z up
inst-in (⟹^S inst up1 up2) = S^ (inst-in inst) up2
inst-in (⟹∙S inst up1 up2) = S∙ (inst-in inst) up2
inst-in (⟹,S inst) = S, (inst-in inst)
inst-in (⟹=S inst up1 up2) = S= (inst-in inst) up2



