module Implicit.Language.Extension.InputOutput where

open import Implicit.Language.Base
open import Implicit.Language.Shift.All
open import Implicit.Language.Lookup.All
open import Implicit.Language.Occur.All
open import Implicit.Language.Extension.Base

----------------------------------------------------------------------
--+                           In and Out                           +--
----------------------------------------------------------------------

extx-^in-=out : Γ ⊆ Δ w/v k
              → Γ ∋^ k
              → Δ ∋= k
extx-^in-=out (ext-Z^ cloA) Z = Z
extx-^in-=out (ext-S, ext) (S, inΓ) = S, (extx-^in-=out ext inΓ)
extx-^in-=out (ext-S^ ext) (S^ inΓ) = S^ (extx-^in-=out ext inΓ)
extx-^in-=out (ext-S∙ ext) (S∙ inΓ) = S∙ (extx-^in-=out ext inΓ)
extx-^in-=out (ext-S= ext) (S= inΓ) = S= (extx-^in-=out ext inΓ)

extx-^in-^out : Γ ⊆ Δ w/v X
              → X ≢ k
              → Γ ∋^ k
              → Δ ∋^ k
extx-^in-^out (ext-Z^ cloA) neq Z = ⊥-elim (neq refl)
extx-^in-^out (ext-Z^ cloA) neq (S^ inΓ) = S= inΓ
extx-^in-^out ext-Z∙ neq inΓ = inΓ
extx-^in-^out ext-Z= neq inΓ = inΓ
extx-^in-^out (ext-S, ext) neq (S, inΓ) = S, (extx-^in-^out ext neq inΓ)
extx-^in-^out (ext-S^ ext) neq Z = Z
extx-^in-^out (ext-S^ ext) neq (S^ inΓ) = S^ (extx-^in-^out ext (≢-pred neq) inΓ)
extx-^in-^out (ext-S∙ ext) neq (S∙ inΓ) = S∙ (extx-^in-^out ext (≢-pred neq) inΓ)
extx-^in-^out (ext-S= ext) neq (S= inΓ) = S= (extx-^in-^out ext (≢-pred neq) inΓ)

extx-=in-=out : Γ ⊆ Δ w/v X
              → Γ ∋= k
              → Δ ∋= k
extx-=in-=out (ext-Z^ cloA) (S^ inΓ) = S= inΓ
extx-=in-=out ext-Z∙ inΓ = inΓ
extx-=in-=out ext-Z= inΓ = inΓ
extx-=in-=out (ext-S, extx) (S, inΓ) = S, (extx-=in-=out extx inΓ)
extx-=in-=out (ext-S^ extx) (S^ inΓ) = S^ (extx-=in-=out extx inΓ)
extx-=in-=out (ext-S∙ extx) (S∙ inΓ) = S∙ (extx-=in-=out extx inΓ)
extx-=in-=out (ext-S= extx) Z = Z
extx-=in-=out (ext-S= extx) (S= inΓ) = S= (extx-=in-=out extx inΓ)

ext-^in-=out : Γ ⊆ Δ w/t A
             → k ε A
             → Γ ∋^ k
             → Δ ∋= k

ext-^in-^out : Γ ⊆ Δ w/t A
             → k ¬ε A
             → Γ ∋^ k
             → Δ ∋^ k

ext-=in-=out : Γ ⊆ Δ w/t A
             → Γ ∋= k
             → Δ ∋= k

ext-^in-=out (ext-var x) ε-var inΓ = extx-^in-=out x inΓ
ext-^in-=out (ext-arr ext ext₁) (ε-arr-l inA) inΓ = ext-=in-=out ext₁ (ext-^in-=out ext inA inΓ)
ext-^in-=out {A = A `→ B} {k = k} (ext-arr ext ext₁) (ε-arr-r inA) inΓ with ε-dec {k = k} {A = A}
... | inj₁ init = ext-=in-=out ext₁ (ext-^in-=out ext init inΓ)
... | inj₂ nint = ext-^in-=out ext₁ inA (ext-^in-^out ext nint inΓ)
ext-^in-=out (ext-∀ ext) (ε-∀ inA) inΓ with ext-^in-=out ext inA (S∙ inΓ)
... | S∙ r = r

ext-^in-^out ext-int ninA inΓ = inΓ
ext-^in-^out (ext-var x) (¬ε-var x₁) inΓ = extx-^in-^out x x₁ inΓ
ext-^in-^out (ext-arr ext ext₁) (¬ε-arr ninA ninA₁) inΓ = ext-^in-^out ext₁ ninA₁ (ext-^in-^out ext ninA inΓ)
ext-^in-^out (ext-∀ ext) (¬ε-∀ ninA) inΓ with ext-^in-^out ext ninA (S∙ inΓ)
... | S∙ r = r

ext-=in-=out ext-int inΓ = inΓ
ext-=in-=out (ext-var x) inΓ = extx-=in-=out x inΓ
ext-=in-=out (ext-arr ext ext₁) inΓ = ext-=in-=out ext₁ (ext-=in-=out ext inΓ)
ext-=in-=out (ext-∀ ext) inΓ with ext-=in-=out ext (S∙ inΓ)
... | S∙ r = r

extx-^in-=out-eq : Γ ⊆ Δ w/v X
                 → Γ ∋^ k
                 → Δ ∋= k
                 → k ≡ X
extx-^in-=out-eq (ext-Z^ cloA) Z inΔ = refl
extx-^in-=out-eq (ext-Z^ cloA) (S^ inΓ) (S= inΔ) = ⊥-elim (∋^-∋=-false inΓ inΔ)
extx-^in-=out-eq ext-Z∙ inΓ inΔ = ⊥-elim (∋^-∋=-false inΓ inΔ)
extx-^in-=out-eq ext-Z= inΓ inΔ = ⊥-elim (∋^-∋=-false inΓ inΔ)
extx-^in-=out-eq (ext-S, ext) (S, inΓ) (S, inΔ) = extx-^in-=out-eq ext inΓ inΔ
extx-^in-=out-eq (ext-S^ ext) (S^ inΓ) (S^ inΔ) = cong #S (extx-^in-=out-eq ext inΓ inΔ)
extx-^in-=out-eq (ext-S∙ ext) (S∙ inΓ) (S∙ inΔ) = cong #S (extx-^in-=out-eq ext inΓ inΔ)
extx-^in-=out-eq (ext-S= ext) (S= inΓ) (S= inΔ) = cong #S (extx-^in-=out-eq ext inΓ inΔ)
