module Implicit.Language.Extension.Occur where

open import Implicit.Language.Base
open import Implicit.Language.Shift.All
open import Implicit.Language.Lookup.All
open import Implicit.Language.Occur.All
open import Implicit.Language.Extension.Base
open import Implicit.Language.Extension.InputOutput
open import Implicit.Language.Extension.ExSol
open import Implicit.Language.Extension.Properties

⊆/x-≢ : Γ ⊆ Δ w/v X
        → Γ ∋^ k
        → Δ ∋^ k
        → X ≢ k
⊆/x-≢ (ext-S^ ext) (S^ inΓ) (S^ inΔ) refl = ⊆/x-≢ ext inΓ inΔ refl
⊆/x-≢ (ext-S∙ ext) (S∙ inΓ) (S∙ inΔ) refl = ⊆/x-≢ ext inΓ inΔ refl
⊆/x-≢ (ext-S= ext regA) (S= inΓ) (S= inΔ) refl = ⊆/x-≢ ext inΓ inΔ refl

⊆-∋^-middle : Γ ∋^ k
            → Δ ∋^ k
            → Γ ⊆ Ω
            → Ω ⊆ Δ
            → Ω ∋^ k
⊆-∋^-middle Z Z (evar ext1) (evar ext2) = Z
⊆-∋^-middle (S∙ inΓ) (S∙ inΔ) (uvar ext1) (uvar ext2) = S∙ (⊆-∋^-middle inΓ inΔ ext1 ext2)
⊆-∋^-middle (S∙ inΓ) (S= inΔ) (uvar ext1) ()
⊆-∋^-middle (S∙ inΓ) (S^ inΔ) (uvar ext1) ()
⊆-∋^-middle (S= inΓ) (S∙ inΔ) (svar ext1 regA) ()
⊆-∋^-middle (S= inΓ) (S= inΔ) (svar ext1 regA) (svar ext2 regA₁) = S= (⊆-∋^-middle inΓ inΔ ext1 ext2)
⊆-∋^-middle (S= inΓ) (S^ inΔ) (svar ext1 regA) ()
⊆-∋^-middle (S^ inΓ) (S∙ inΔ) (evar ext1) ()
⊆-∋^-middle (S^ inΓ) (S∙ inΔ) (evar-sol ext1 regA) ()
⊆-∋^-middle (S^ inΓ) (S= inΔ) (evar ext1) (evar-sol ext2 regA) = S^ (⊆-∋^-middle inΓ inΔ ext1 ext2)
⊆-∋^-middle (S^ inΓ) (S= inΔ) (evar-sol ext1 regA) (svar ext2 regA₁) = S= (⊆-∋^-middle inΓ inΔ ext1 ext2)
⊆-∋^-middle (S^ inΓ) (S^ inΔ) (evar ext1) (evar ext2) = S^ (⊆-∋^-middle inΓ inΔ ext1 ext2)


^in-^out-¬ε : Γ ⊆ Δ w/t A
            → Γ ∋^ k
            → Δ ∋^ k
            → k ¬ε A
^in-^out-¬ε (ext-int x) inΓ inΔ = ¬ε-int
^in-^out-¬ε (ext-var x) inΓ inΔ = ¬ε-var (⊆/x-≢ x inΓ inΔ)
^in-^out-¬ε (ext-arr ext ext₁) inΓ inΔ = let inΩ = ⊆-∋^-middle inΓ inΔ (⊆/-⊆ ext₁) (⊆/-⊆ ext)
                                         in ¬ε-arr (^in-^out-¬ε ext inΩ inΔ) (^in-^out-¬ε ext₁ inΓ inΩ)
^in-^out-¬ε (ext-∀ ext) inΓ inΔ = ¬ε-∀ (^in-^out-¬ε ext (S∙ inΓ) (S∙ inΔ))


^in-=out-ε : Γ ⊆ Δ w/t A
           → Γ ∋^ k
           → Δ ∋= k
           → k ε A
^in-=out-ε (ext-int regΓ) inΓ inΔ = ⊥-elim (∋^-∋=-false inΓ inΔ)
^in-=out-ε (ext-var x) inΓ inΔ with ⊆/x-^in-=out-eq x inΓ inΔ
... | refl = ε-var
^in-=out-ε (ext-arr ext ext₁) inΓ inΔ with ⊆/-exsol ext₁ inΓ
... | is-ex inΓ₁ = ε-arr-l (^in-^out-¬ε ext₁ inΓ inΓ₁) (^in-=out-ε ext inΓ₁ inΔ)
... | is-sol inΓ₁ = ε-arr-r (^in-=out-ε ext₁ inΓ inΓ₁)
^in-=out-ε (ext-∀ ext) inΓ inΔ = ε-∀ (^in-=out-ε ext (S∙ inΓ) (S∙ inΔ))
