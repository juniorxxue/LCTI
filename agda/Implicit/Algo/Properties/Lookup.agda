module Implicit.Algo.Properties.Lookup where

open import Implicit.Language
open import Implicit.Algo.Base

private variable
  A A' B C : Type m
  k k₁ k₂ : Fin m
  Σ Σ' : Context n m
  Ψ Ψ' : SEnv n m

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

:=to= : k := A ∈ Ψ
        → k =∈ Ψ
:=to= (Z up) = Z
:=to= (S, inΨ) = S, (:=to= inΨ)
:=to= (S^ inΨ up) = S^ (:=to= inΨ)
:=to= (S∙ inΨ up) = S∙ (:=to= inΨ)
:=to= (S= inΨ up) = S= (:=to= inΨ)


----------------------------------------------------------------------
--+                           Extension                            +--
----------------------------------------------------------------------

⊆-in:= : k := C ∈ Ψ
       → Ψ ⊆ Ψ'
       → k := C ∈ Ψ'
⊆-in:= (Z x) (svar ss) = Z x
⊆-in:= (S, inΨ) (var ss) = S, (⊆-in:= inΨ ss)
⊆-in:= (S^ inΨ x) (evar ss) = S^ (⊆-in:= inΨ ss) x
⊆-in:= (S^ inΨ x) (evar-sol {A = A} ss) = S= (⊆-in:= inΨ ss) x
⊆-in:= (S∙ inΨ x) (uvar ss) = S∙ (⊆-in:= inΨ ss) x
⊆-in:= (S= inΨ st) (svar ss) = S= (⊆-in:= inΨ ss) st

⊆-in= : k =∈ Ψ
      → Ψ ⊆ Ψ'
      → k =∈ Ψ'
⊆-in= Z (svar ss) = Z
⊆-in= (S, inΨ) (var ss) = S, (⊆-in= inΨ ss)
⊆-in= (S^ inΨ) (evar ss) = S^ (⊆-in= inΨ ss)
⊆-in= (S^ inΨ) (evar-sol ss) = S= (⊆-in= inΨ ss)
⊆-in= (S∙ inΨ) (uvar ss) = S∙ (⊆-in= inΨ ss)
⊆-in= (S= inΨ) (svar ss) = S= (⊆-in= inΨ ss)

⊆-in∙ : k ∙∈ Ψ
      → Ψ ⊆ Ψ'
      → k ∙∈ Ψ'
⊆-in∙ Z (uvar ss) = Z
⊆-in∙ (S^ inΨ) (evar ss) = S^ (⊆-in∙ inΨ ss)
⊆-in∙ (S^ inΨ) (evar-sol ss) = S= (⊆-in∙ inΨ ss)
⊆-in∙ (S∙ inΨ) (uvar ss) = S∙ (⊆-in∙ inΨ ss)
⊆-in∙ (S, inΨ) (var ss) = S, (⊆-in∙ inΨ ss)
⊆-in∙ (S= inΨ) (svar ss) = S= (⊆-in∙ inΨ ss)
