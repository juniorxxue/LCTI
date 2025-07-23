module Implicit.Language.Extension.ExSol where

open import Implicit.Language.Base
open import Implicit.Language.Shift.All
open import Implicit.Language.Lookup.All
open import Implicit.Language.Occur.All
open import Implicit.Language.Extension.Base
open import Implicit.Language.Extension.InputOutput

s-⊆-exsol : Γ ⊆ Δ
          → Γ ∋^ k
          → ExSol Δ k
s-⊆-exsol (uvar ext) (S∙ inΓ) with s-⊆-exsol ext inΓ
... | is-ex x = is-ex (S∙ x)
... | is-sol x = is-sol (S∙ x)
s-⊆-exsol (evar ext) Z = is-ex Z
s-⊆-exsol (evar ext) (S^ inΓ) with s-⊆-exsol ext inΓ
... | is-ex x = is-ex (S^ x)
... | is-sol x = is-sol (S^ x)
s-⊆-exsol (evar-sol ext cloA) Z = is-sol Z
s-⊆-exsol (evar-sol ext cloA) (S^ inΓ) with s-⊆-exsol ext inΓ
... | is-ex x = is-ex (S= x)
... | is-sol x = is-sol (S= x)
s-⊆-exsol (svar ext _) (S= inΓ) with s-⊆-exsol ext inΓ
... | is-ex x = is-ex (S= x)
... | is-sol x = is-sol (S= x)
s-⊆-exsol (tvar ext regA) (S, inΓ) with s-⊆-exsol ext inΓ
... | is-ex inΓ₁ = is-ex (S, inΓ₁)
... | is-sol inΓ₁ = is-sol (S, inΓ₁)

⊆/x-exsol : Γ ⊆ Δ w/v X
          → Γ ∋^ k
          → ExSol Δ k
⊆/x-exsol (ext-Z^ _ cloA) Z = is-sol Z
⊆/x-exsol (ext-Z^ _ cloA) (S^ inΓ) = is-ex (S= inΓ)
⊆/x-exsol (ext-Z∙ _) (S∙ inΓ) = is-ex (S∙ inΓ)
⊆/x-exsol (ext-Z= _ _) (S= inΓ) = is-ex (S= inΓ)
⊆/x-exsol (ext-S^ ext) Z = is-ex Z
⊆/x-exsol (ext-S^ ext) (S^ inΓ) with ⊆/x-exsol ext inΓ
... | is-ex inΓ₁ = is-ex (S^ inΓ₁)
... | is-sol inΓ₁ = is-sol (S^ inΓ₁)
⊆/x-exsol (ext-S∙ ext) (S∙ inΓ) with ⊆/x-exsol ext inΓ
... | is-ex inΓ₁ = is-ex (S∙ inΓ₁)
... | is-sol inΓ₁ = is-sol (S∙ inΓ₁)
⊆/x-exsol (ext-S= ext _) (S= inΓ) with ⊆/x-exsol ext inΓ
... | is-ex inΓ₁ = is-ex (S= inΓ₁)
... | is-sol inΓ₁ = is-sol (S= inΓ₁)

⊆/-exsol : Γ ⊆ Δ w/t A
         → Γ ∋^ k
         → ExSol Δ k
⊆/-exsol (ext-int _) inΓ = is-ex inΓ
⊆/-exsol (ext-var x) inΓ = ⊆/x-exsol x inΓ
⊆/-exsol (ext-arr ext ext₁) inΓ with ⊆/-exsol ext inΓ
... | is-ex inΓ₁ with ⊆/-exsol ext₁ inΓ₁
... | is-ex inΓ₂ = is-ex inΓ₂
... | is-sol inΓ₂ = is-sol inΓ₂
⊆/-exsol (ext-arr ext ext₁) inΓ | is-sol inΓ₁ = is-sol (⊆/-=in-=out ext₁ inΓ₁)
⊆/-exsol (ext-∀ ext) inΓ with ⊆/-exsol ext (S∙ inΓ)
... | is-ex (S∙ inΓ₁) = is-ex inΓ₁
... | is-sol (S∙ inΓ₁) = is-sol inΓ₁
