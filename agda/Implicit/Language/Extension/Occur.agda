module Implicit.Language.Extension.Occur where

open import Implicit.Language.Base
open import Implicit.Language.Shift.All
open import Implicit.Language.Lookup.All
open import Implicit.Language.Occur.All
open import Implicit.Language.Extension.Base
open import Implicit.Language.Extension.InputOutput
open import Implicit.Language.Extension.ExSol

^in-=out-ε : Γ ⊆ Δ w/t A
           → Γ ∋^ k
           → Δ ∋= k
           → k ε A
^in-=out-ε ext-int inΓ inΔ = ⊥-elim (∋^-∋=-false inΓ inΔ)
^in-=out-ε (ext-var x) inΓ inΔ with extx-^in-=out-eq x inΓ inΔ
... | refl = ε-var
^in-=out-ε (ext-arr ext ext₁) inΓ inΔ with ⊆/-exsol ext inΓ
... | is-ex inΓ₁ = ε-arr-r (^in-=out-ε ext₁ inΓ₁ inΔ)
... | is-sol inΓ₁ = ε-arr-l (^in-=out-ε ext inΓ inΓ₁)
^in-=out-ε (ext-∀ ext) inΓ inΔ = ε-∀ (^in-=out-ε ext (S∙ inΓ) (S∙ inΔ))
