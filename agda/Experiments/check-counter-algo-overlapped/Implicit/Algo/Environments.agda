module Implicit.Algo.Environments where

open import Implicit.Common
open import Implicit.Properties
open import Implicit.Algo

inst-in : ∀ {Ψ Ψ' : SEnv n m} {A X}
  → [ A / X ] Ψ ⟹ Ψ'
  → X := A ∈ Ψ'
inst-in ⟹^0 = Z
inst-in (⟹^S ist) = S^ (inst-in ist)
inst-in (⟹∙S ist) = S∙ (inst-in ist)
inst-in (⟹,S ist) = S, (inst-in ist)
inst-in (⟹=S ist) = S= (inst-in ist)
