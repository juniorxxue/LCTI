module Implicit.Algo.Properties.Environments where

open import Implicit.Language
open import Implicit.Algo.Base
open import Implicit.Algo.Properties.Extension
open import Implicit.Algo.Properties.OpenClose
open import Implicit.Algo.Properties.Lookup

private variable
  Ψ Ψ' : SEnv n m
  A B C D : Type m
  k X : Fin m
  Σ : Context n m
  e : Term n m
  ≤ : Polar

----------------------------------------------------------------------
--+                          Small Lemmas                          +--
----------------------------------------------------------------------
inst-in : ∀ {X}
  → [ A / X ] Ψ ⟹ Ψ'
  → X =∈ Ψ'
inst-in (⟹^0 up) = Z
inst-in (⟹^S inst up) = S^ (inst-in inst)
inst-in (⟹∙S inst up) = S∙ (inst-in inst)
inst-in (⟹,S inst) = S, (inst-in inst)
inst-in (⟹=S up inst) = S= (inst-in inst)


-- a correct version
postulate
  inst-s : [ A / X ] Ψ ⟹ Ψ'
         → Ψ' ⊢ ‶ X ⌞ ≤ ⌝ τ A ⊣ Ψ' ↪ A

----------------------------------------------------------------------
--+                   Lemmas around env extension                  +--
----------------------------------------------------------------------





----------------------------------------------------------------------
--+ Invariant: appearing existentials must be solved in output env +--
----------------------------------------------------------------------

s-out-closed-l : Ψ ⊢ A ⌞ ≤ ⌝ Σ ⊣ Ψ' ↪ B
               → Polarity Ψ A Σ ≤
               → Ψ' ⊢c A

s-out-closed-r : Ψ ⊢ A ⌞ ≤ ⌝ Σ ⊣ Ψ' ↪ B
               → Polarity Ψ A Σ ≤
               → Ψ' ⊢cᶜ Σ
               
s-out-closed-l s-int pr = ⊢c-int
s-out-closed-l (s-empty p) pr = p
s-out-closed-l (s-var clo) pr = clo
s-out-closed-l (s-ex-l^ clo x-in inst) pr = {!!}
s-out-closed-l (s-ex-l= clo x-in s) pr = {!!}
s-out-closed-l (s-ex-r^ clo x-in inst) pr = {!!}
s-out-closed-l (s-ex-r= clo x-in s) pr = {!!}
s-out-closed-l (s-arr s s₁) pr with s-out-closed-r s (polar-arr-l pr)
... | ⊢c-τ cloA = ⊢c-arr {!!} (s-out-closed-l s₁ (polar-arr-r {!!}))
s-out-closed-l (s-term-c cloA ⊢e s) pr = {!!}
s-out-closed-l (s-term-o opnA ⊢e s s₁) pr = {!!}
s-out-closed-l (s-∀ s) pr = {!!}
s-out-closed-l (s-∀l s upᶜ upᵉ st₁ st₂) pr = {!!}

