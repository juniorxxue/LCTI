module Implicit.Algo.Properties.Lookup where

open import Implicit.Language
open import Implicit.Algo.Base

private variable
  A A' B C : Type m
  k k₁ k₂ : Fin m
  Σ Σ' : Context n m
  Γ Γ' : Env n m

ε-↑ty : k₁ ε A
      → A ↑ty k₂ ⇘ A'
      → k₂ #≤ k₁
      → #S k₁ ε A'
ε-↑ty ε-var ↑ty-var sm rewrite punchIn-≤ sm = ε-var
ε-↑ty (ε-arr-l kε) (↑ty-arr ↑ty ↑ty₁) sm = ε-arr-l (ε-↑ty kε ↑ty sm)
ε-↑ty (ε-arr-r kε) (↑ty-arr ↑ty ↑ty₁) sm = ε-arr-r (ε-↑ty kε ↑ty₁ sm)
ε-↑ty (ε-∀ kε) (↑ty-∀ ↑ty) sm = ε-∀ (ε-↑ty kε ↑ty (s≤s sm))

ε-↑ty0 : k ε A
       → ↑ty0 A ⇘ A'
       → #S k ε A'
ε-↑ty0 inA ↑ty = ε-↑ty inA ↑ty z≤n


εᶜ-↑tyᶜ : k₁ εᶜ Σ
        → Σ ↑tyᶜ k₂ ⇘ Σ'
        → k₂ #≤ k₁
        → #S k₁ εᶜ Σ'
εᶜ-↑tyᶜ (^∈-type inA) (↑tyᶜ-τ up-t) sm = ^∈-type (ε-↑ty inA up-t sm)
εᶜ-↑tyᶜ (^∈-term kεᶜ) (↑tyᶜ-e up-e upc) sm = ^∈-term (εᶜ-↑tyᶜ kεᶜ upc sm)

εᶜ-↑tyᶜ0 : k εᶜ Σ
        → ↑tyᶜ0 Σ ⇘ Σ'
        → #S k εᶜ Σ'
εᶜ-↑tyᶜ0 k-in up-c = εᶜ-↑tyᶜ k-in up-c z≤n

:=to= : Γ ∋ k := A
      → Γ ∋= k
:=to= (Z up) = Z
:=to= (S, inΓ) = S, (:=to= inΓ)
:=to= (S^ inΓ up) = S^ (:=to= inΓ)
:=to= (S∙ inΓ up) = S∙ (:=to= inΓ)
:=to= (S= inΓ up) = S= (:=to= inΓ)


----------------------------------------------------------------------
--+                           Extension                            +--
----------------------------------------------------------------------

⊆-in:= : Γ ∋ k := C
       → Γ ⊆ Γ'
       → Γ' ∋ k := C
⊆-in:= (Z x) (svar ss) = Z x
⊆-in:= (S, inΓ) (var ss) = S, (⊆-in:= inΓ ss)
⊆-in:= (S^ inΓ x) (evar ss) = S^ (⊆-in:= inΓ ss) x
⊆-in:= (S^ inΓ x) (evar-sol {A = A} ss) = S= (⊆-in:= inΓ ss) x
⊆-in:= (S∙ inΓ x) (uvar ss) = S∙ (⊆-in:= inΓ ss) x
⊆-in:= (S= inΓ st) (svar ss) = S= (⊆-in:= inΓ ss) st

⊆-in= : Γ ∋= k
      → Γ ⊆ Γ'
      → Γ' ∋= k
⊆-in= Z (svar ss) = Z
⊆-in= (S, inΓ) (var ss) = S, (⊆-in= inΓ ss)
⊆-in= (S^ inΓ) (evar ss) = S^ (⊆-in= inΓ ss)
⊆-in= (S^ inΓ) (evar-sol ss) = S= (⊆-in= inΓ ss)
⊆-in= (S∙ inΓ) (uvar ss) = S∙ (⊆-in= inΓ ss)
⊆-in= (S= inΓ) (svar ss) = S= (⊆-in= inΓ ss)

⊆-in∙ : Γ ∋∙ k
      → Γ ⊆ Γ'
      → Γ' ∋∙ k
⊆-in∙ Z (uvar ss) = Z
⊆-in∙ (S^ inΓ) (evar ss) = S^ (⊆-in∙ inΓ ss)
⊆-in∙ (S^ inΓ) (evar-sol ss) = S= (⊆-in∙ inΓ ss)
⊆-in∙ (S∙ inΓ) (uvar ss) = S∙ (⊆-in∙ inΓ ss)
⊆-in∙ (S, inΓ) (var ss) = S, (⊆-in∙ inΓ ss)
⊆-in∙ (S= inΓ) (svar ss) = S= (⊆-in∙ inΓ ss)
