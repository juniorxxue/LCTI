module Implicit.Language.Extension.InputOutput where

open import Implicit.Language.Base
open import Implicit.Language.Shift.All
open import Implicit.Language.Lookup.All
open import Implicit.Language.Occur.All
open import Implicit.Language.Extension.Base

----------------------------------------------------------------------
--+                           In and Out                           +--
----------------------------------------------------------------------

⊆/x-^in-=out : Γ ⊆ Δ w/v k
              → Γ ∋^ k
              → Δ ∋= k
⊆/x-^in-=out (ext-Z^ _ cloA) Z = Z
⊆/x-^in-=out (ext-S^ ext) (S^ inΓ) = S^ (⊆/x-^in-=out ext inΓ)
⊆/x-^in-=out (ext-S∙ ext) (S∙ inΓ) = S∙ (⊆/x-^in-=out ext inΓ)
⊆/x-^in-=out (ext-S= ext _) (S= inΓ) = S= (⊆/x-^in-=out ext inΓ)

⊆/x-^in-^out : Γ ⊆ Δ w/v X
              → X ≢ k
              → Γ ∋^ k
              → Δ ∋^ k
⊆/x-^in-^out (ext-Z^ _ cloA) neq Z = ⊥-elim (neq refl)
⊆/x-^in-^out (ext-Z^ _ cloA) neq (S^ inΓ) = S= inΓ
⊆/x-^in-^out (ext-Z∙ _) neq inΓ = inΓ
⊆/x-^in-^out (ext-Z= _ _) neq inΓ = inΓ
⊆/x-^in-^out (ext-S^ ext) neq Z = Z
⊆/x-^in-^out (ext-S^ ext) neq (S^ inΓ) = S^ (⊆/x-^in-^out ext (≢-pred neq) inΓ)
⊆/x-^in-^out (ext-S∙ ext) neq (S∙ inΓ) = S∙ (⊆/x-^in-^out ext (≢-pred neq) inΓ)
⊆/x-^in-^out (ext-S= ext _) neq (S= inΓ) = S= (⊆/x-^in-^out ext (≢-pred neq) inΓ)

⊆/x-=in-=out : Γ ⊆ Δ w/v X
              → Γ ∋= k
              → Δ ∋= k
⊆/x-=in-=out (ext-Z^ _ cloA) (S^ inΓ) = S= inΓ
⊆/x-=in-=out (ext-Z∙ _) inΓ = inΓ
⊆/x-=in-=out (ext-Z= _ _) inΓ = inΓ
⊆/x-=in-=out (ext-S^ extx) (S^ inΓ) = S^ (⊆/x-=in-=out extx inΓ)
⊆/x-=in-=out (ext-S∙ extx) (S∙ inΓ) = S∙ (⊆/x-=in-=out extx inΓ)
⊆/x-=in-=out (ext-S= _ extx) Z = Z
⊆/x-=in-=out (ext-S= extx _) (S= inΓ) = S= (⊆/x-=in-=out extx inΓ)

⊆/-^in-=out : Γ ⊆ Δ w/t A
             → k ε A
             → Γ ∋^ k
             → Δ ∋= k

⊆/-^in-^out : Γ ⊆ Δ w/t A
             → k ¬ε A
             → Γ ∋^ k
             → Δ ∋^ k

⊆/-=in-=out : Γ ⊆ Δ w/t A
             → Γ ∋= k
             → Δ ∋= k

⊆/-^in-=out (ext-var x) ε-var inΓ = ⊆/x-^in-=out x inΓ
⊆/-^in-=out (ext-arr ext ext₁) (ε-arr-l inA) inΓ = ⊆/-=in-=out ext₁ (⊆/-^in-=out ext inA inΓ)
⊆/-^in-=out {A = A `→ B} {k = k} (ext-arr ext ext₁) (ε-arr-r inB) inΓ with ε-dec {k = k} {A = A}
... | inj₁ init = ⊆/-=in-=out ext₁ (⊆/-^in-=out ext init inΓ)
... | inj₂ nint = ⊆/-^in-=out ext₁ inB (⊆/-^in-^out ext nint inΓ)
⊆/-^in-=out (ext-∀ ext) (ε-∀ inA) inΓ with ⊆/-^in-=out ext inA (S∙ inΓ)
... | S∙ r = r
⊆/-^in-=out {A = A `→ B} {k = k} (ext-arr-n x₁ x₂) (ε-arr-l x₃) x with ε-dec {k = k} {A = B}
... | inj₁ init = ⊆/-=in-=out x₂ (⊆/-^in-=out x₁ init x)
... | inj₂ nint = ⊆/-^in-=out x₂ x₃ (⊆/-^in-^out x₁ nint x)
⊆/-^in-=out (ext-arr-n x₁ x₂) (ε-arr-r x₃) x = ⊆/-=in-=out x₂ (⊆/-^in-=out x₁ x₃ x)

⊆/-^in-^out (ext-int _) ninA inΓ = inΓ
⊆/-^in-^out (ext-var x) (¬ε-var x₁) inΓ = ⊆/x-^in-^out x x₁ inΓ
⊆/-^in-^out (ext-arr ext ext₁) (¬ε-arr ninA ninA₁) inΓ = ⊆/-^in-^out ext₁ ninA₁ (⊆/-^in-^out ext ninA inΓ)
⊆/-^in-^out (ext-∀ ext) (¬ε-∀ ninA) inΓ with ⊆/-^in-^out ext ninA (S∙ inΓ)
... | S∙ r = r
⊆/-^in-^out (ext-arr-n x₂ x₃) (¬ε-arr x x₄) x₁ = ⊆/-^in-^out x₃ x (⊆/-^in-^out x₂ x₄ x₁)

⊆/-=in-=out (ext-int _) inΓ = inΓ
⊆/-=in-=out (ext-var x) inΓ = ⊆/x-=in-=out x inΓ
⊆/-=in-=out (ext-arr ext ext₁) inΓ = ⊆/-=in-=out ext₁ (⊆/-=in-=out ext inΓ)
⊆/-=in-=out (ext-∀ ext) inΓ with ⊆/-=in-=out ext (S∙ inΓ)
... | S∙ r = r
⊆/-=in-=out (ext-arr-n x₁ x₂) x = ⊆/-=in-=out x₂ (⊆/-=in-=out x₁ x)

⊆/x-^in-=out-eq : Γ ⊆ Δ w/v X
                 → Γ ∋^ k
                 → Δ ∋= k
                 → k ≡ X
⊆/x-^in-=out-eq (ext-Z^ _ cloA) Z inΔ = refl
⊆/x-^in-=out-eq (ext-Z^ _ cloA) (S^ inΓ) (S= inΔ) = ⊥-elim (∋^-∋=-false inΓ inΔ)
⊆/x-^in-=out-eq (ext-Z∙ _) inΓ inΔ = ⊥-elim (∋^-∋=-false inΓ inΔ)
⊆/x-^in-=out-eq (ext-Z= _ _) inΓ inΔ = ⊥-elim (∋^-∋=-false inΓ inΔ)
⊆/x-^in-=out-eq (ext-S^ ext) (S^ inΓ) (S^ inΔ) = cong #S (⊆/x-^in-=out-eq ext inΓ inΔ)
⊆/x-^in-=out-eq (ext-S∙ ext) (S∙ inΓ) (S∙ inΔ) = cong #S (⊆/x-^in-=out-eq ext inΓ inΔ)
⊆/x-^in-=out-eq (ext-S= ext _) (S= inΓ) (S= inΔ) = cong #S (⊆/x-^in-=out-eq ext inΓ inΔ)

⊆/x-=out-in : Γ ⊆ Δ w/v k
            → Δ ∋= k
            → ExSol Γ k
⊆/x-=out-in (ext-Z^ regΓ regA) Z = is-ex Z
⊆/x-=out-in (ext-Z= regΓ regA) Z = is-sol Z
⊆/x-=out-in (ext-S^ ext) (S^ inΔ) with ⊆/x-=out-in ext inΔ
... | is-ex inΓ = is-ex (S^ inΓ)
... | is-sol inΓ = is-sol (S^ inΓ)
⊆/x-=out-in (ext-S∙ ext) (S∙ inΔ) with ⊆/x-=out-in ext inΔ
... | is-ex inΓ = is-ex (S∙ inΓ)
... | is-sol inΓ = is-sol (S∙ inΓ)
⊆/x-=out-in (ext-S= ext regA) (S= inΔ) with ⊆/x-=out-in ext inΔ
... | is-ex inΓ = is-ex (S= inΓ)
... | is-sol inΓ = is-sol (S= inΓ)
