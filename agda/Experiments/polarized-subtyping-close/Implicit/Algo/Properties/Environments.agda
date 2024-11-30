module Implicit.Algo.Properties.Environments where

open import Implicit.Language
open import Implicit.Algo.Base
open import Implicit.Algo.Properties.Extension
open import Implicit.Algo.Properties.OpenClose
open import Implicit.Algo.Properties.Lookup

private variable
  Ψ Ψ' : SEnv n m
  A B C : Type m
  k : Fin m
  Σ : Context n m
  e : Term n m

----------------------------------------------------------------------
--+                          Small Lemmas                          +--
----------------------------------------------------------------------

inst-in : ∀ {X}
  → [ A / X ] Ψ ⟹ Ψ'
  → X := A ∈ Ψ'
inst-in (⟹^0 x) = Z x
inst-in (⟹^S st x) = S^ (inst-in st) x
inst-in (⟹∙S st x) = S∙ (inst-in st) x
inst-in (⟹,S st) = S, (inst-in st)
inst-in (⟹=S up st) = S= (inst-in st) up

----------------------------------------------------------------------
--+                   Lemmas around env extension                  +--
----------------------------------------------------------------------

⊆-in= : k := C ∈ Ψ
      → Ψ ⊆ Ψ'
      → k := C ∈ Ψ'
⊆-in= (Z x) (svar ss) = Z x
⊆-in= (S, inΨ) (var ss) = S, (⊆-in= inΨ ss)
⊆-in= (S^ inΨ x) (evar ss) = S^ (⊆-in= inΨ ss) x
⊆-in= (S^ inΨ x) (evar-sol {A = A} ss) = S= (⊆-in= inΨ ss) (↑ty-st x)
⊆-in= (S∙ inΨ x) (uvar ss) = S∙ (⊆-in= inΨ ss) x
⊆-in= (S= inΨ st) (svar ss) = S= (⊆-in= inΨ ss) st

⊆-in∙ : k ∙∈ Ψ
      → Ψ ⊆ Ψ'
      → k ∙∈ Ψ'
⊆-in∙ Z (uvar ss) = Z
⊆-in∙ (S^ inΨ) (evar ss) = S^ (⊆-in∙ inΨ ss)
⊆-in∙ (S^ inΨ) (evar-sol ss) = S= (⊆-in∙ inΨ ss)
⊆-in∙ (S∙ inΨ) (uvar ss) = S∙ (⊆-in∙ inΨ ss)
⊆-in∙ (S, inΨ) (var ss) = S, (⊆-in∙ inΨ ss)
⊆-in∙ (S= inΨ) (svar ss) = S= (⊆-in∙ inΨ ss)

⊆-closed : Ψ ⊢c A
         → Ψ ⊆ Ψ'
         → Ψ' ⊢c A
⊆-closed ⊢c-int ss = ⊢c-int
⊆-closed (⊢c-var-∙ x) ss = ⊢c-var-∙ (⊆-in∙ x ss)
⊆-closed (⊢c-var-= x) ss = ⊢c-var-= (⊆-in= x ss)
⊆-closed (⊢c-arr clo clo₁) ss = ⊢c-arr (⊆-closed clo ss) (⊆-closed clo₁ ss)
⊆-closed (⊢c-∀ clo) ss = ⊢c-∀ (⊆-closed clo (uvar ss))

⊆-closedᶜ : Ψ ⊢cᶜ Σ
          → Ψ ⊆ Ψ'
          → Ψ' ⊢cᶜ Σ
⊆-closedᶜ ⊢c-empty ss = ⊢c-empty
⊆-closedᶜ (⊢c-τ cloA) ss = ⊢c-τ (⊆-closed cloA ss)
⊆-closedᶜ (⊢c-term clo) ss = ⊢c-term (⊆-closedᶜ clo ss)


----------------------------------------------------------------------
--+ Invariant: appearing existentials must be solved in output env +--
----------------------------------------------------------------------

-- I realise that I probably want to show that A and Σ is closed under Ψ'
-- I think it should be a corollary of the following lemma
-- but not sure, whether directly prove this lemma is easier

s⁺-out-closed-r : Ψ ⊢ A ≤⁺ Σ ⊣ Ψ' ↪ B
                → Ψ' ⊢cᶜ Σ
s⁺-out-closed-r s = ⊆-closedᶜ (polarity⁺ s) (s⁺-⊆ s)

s⁻-out-closed-l : Ψ ⊢ A ≤⁻ Σ ⊣ Ψ' ↪ B
                → Ψ' ⊢c A
s⁻-out-closed-l s = ⊆-closed (polarity⁻ s) (s⁻-⊆ s)                

s⁺-out-closed-l : Ψ ⊢ A ≤⁺ Σ ⊣ Ψ' ↪ B
                → Ψ' ⊢c A

s⁻-out-closed-r : Ψ ⊢ A ≤⁻ Σ ⊣ Ψ' ↪ B
                → Ψ' ⊢cᶜ Σ

s⁺-out-closed-l s⁺-int = ⊢c-int
s⁺-out-closed-l (s⁺-empty cloA) = cloA
s⁺-out-closed-l (s⁺-var cloX) = cloX
s⁺-out-closed-l (s⁺-ex-l^ cloA x-in inst) = ⊢c-var-= (inst-in inst)
s⁺-out-closed-l (s⁺-ex-l= cloA x-in s) = ⊆-closed (⊢c-var-= x-in) (s⁺-⊆ s)
s⁺-out-closed-l (s⁺-ex-r= cloA x-in s) = s⁺-out-closed-l s
s⁺-out-closed-l (s⁺-arr cloC cloD s s₁) with s⁻-out-closed-r s
... | ⊢c-τ cloA = ⊢c-arr (⊆-closed cloA (s⁺-⊆ s₁)) (s⁺-out-closed-l s₁)
s⁺-out-closed-l (s⁺-term-c cloA cloΣ ⊢e s) = ⊢c-arr (⊆-closed cloA (s⁺-⊆ s)) (s⁺-out-closed-l s)
s⁺-out-closed-l (s⁺-term-o opnA cloΣ ⊢e s s₁) with s⁻-out-closed-r s
... | ⊢c-τ cloA = ⊢c-arr (⊆-closed cloA (s⁺-⊆ s₁)) (s⁺-out-closed-l s₁)
s⁺-out-closed-l (s⁺-∀ cloB s) = ⊢c-∀ (s⁺-out-closed-l s)
s⁺-out-closed-l (s⁺-∀l cloΣ s upᶜ upᵉ st₁ st₂) with s⁺-out-closed-l s
... | r = {!!}

s⁻-out-closed-r s = {!!}

