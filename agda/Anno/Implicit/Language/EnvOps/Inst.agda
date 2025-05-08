module Implicit.Language.EnvOps.Inst where

open import Implicit.Language.Base
open import Implicit.Language.Shift.All
open import Implicit.Language.Lookup.All
open import Implicit.Language.Regular.Base
open import Implicit.Language.OpenClose.Base
open import Implicit.Language.Ground.Base
open import Implicit.Language.EnvOps.Base


-- replace entry ^a with a solution ^a=A in an environment
infix 3 [_/_]_⟹_
data [_/_]_⟹_ : Type m → Fin m → Env n m → Env n m → Set where
  ⟹^0 : (up : ↑ty0 A ⇘ A')
        → (regA : Γ ⊢r A)
        → (env : SRegular Γ)
        → [ A' / #0 ] (Γ ,^) ⟹ (Γ ,= A)

  ⟹^S : [ A / k ] Γ ⟹ Γ'
        → (up1 : ↑ty0 A ⇘ A')
        → [ A' / #S k ] (Γ ,^) ⟹ Γ' ,^

  ⟹∙S : [ A / k ] Γ ⟹ Γ'
        → (up1 : ↑ty0 A ⇘ A')
        → [ A' / #S k ] (Γ ,∙) ⟹ (Γ' ,∙)

  ⟹=S : [ A / k ] Γ ⟹ Γ'
        → (up1 : ↑ty0 A ⇘ A')
        → (regB : Γ ⊢r B)
        → [ A' / #S k ] (Γ ,= B) ⟹ (Γ' ,= B)

inst-∋^ : [ A / k ] Γ ⟹ Δ
        → Γ ∋^ k
inst-∋^ (⟹^0 up regA env) = Z
inst-∋^ (⟹^S inst up1) = S^ (inst-∋^ inst)
inst-∋^ (⟹∙S inst up1) = S∙ (inst-∋^ inst)
inst-∋^ (⟹=S inst up1 regB) = S= (inst-∋^ inst)

inst-∋= : [ A / k ] Γ ⟹ Δ
        → Δ ∋= k
inst-∋= (⟹^0 up regA env) = Z
inst-∋= (⟹^S inst up1) = S^ (inst-∋= inst)
inst-∋= (⟹∙S inst up1) = S∙ (inst-∋= inst)
inst-∋= (⟹=S inst up1 regB) = S= (inst-∋= inst)

inst-∋:= : [ A / k ] Γ ⟹ Δ
         → Δ ∋ k := A
inst-∋:= (⟹^0 up regA env) = Z up
inst-∋:= (⟹^S inst up1) = S^ (inst-∋:= inst) up1
inst-∋:= (⟹∙S inst up1) = S∙ (inst-∋:= inst) up1
inst-∋:= (⟹=S inst up1 regB) = S= (inst-∋:= inst) up1
