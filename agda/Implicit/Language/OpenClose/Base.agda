module Implicit.Language.OpenClose.Base where

open import Implicit.Language.Base
open import Implicit.Language.Lookup.All
open import Implicit.Language.Regular.Base

infix 3 _⊢o_
-- open: have free existential variables
data _⊢o_ : Env n m → Type m → Set where
  ⊢o-var-^ :
      Δ ∋^ X
    → Δ ⊢o ‶ X
  ⊢o-arr-l :
      Δ ⊢o A
    → Δ ⊢o (A `→ B)
  ⊢o-arr-r :
      Δ ⊢o B
    → Δ ⊢o (A `→ B)
  ⊢o-∀ :
      Δ ,∙ ⊢o A
    → Δ ⊢o `∀ A

⊢r-⊢o-false : Γ ⊢r A
            → Γ ⊢o A
            → ⊥
⊢r-⊢o-false (⊢r-var-∙ inΓ) (⊢o-var-^ x) = ∋^-∋∙-false x inΓ
⊢r-⊢o-false (⊢r-arr regA regA₁) (⊢o-arr-l opnA) = ⊢r-⊢o-false regA opnA
⊢r-⊢o-false (⊢r-arr regA regA₁) (⊢o-arr-r opnA) = ⊢r-⊢o-false regA₁ opnA
⊢r-⊢o-false (⊢r-∀ regA) (⊢o-∀ opnA) = ⊢r-⊢o-false regA opnA


infix 3 _⊢c_
data _⊢c_ : Env n m → Type m → Set where
  ⊢c-int :
      Δ ⊢c Int
  ⊢c-var-∙ :
      (inΔ : Δ ∋∙ X)
    → Δ ⊢c ‶ X
  ⊢c-var-= :
      (inΔ : Δ ∋= X)
    → Δ ⊢c ‶ X
  ⊢c-arr :
      Δ ⊢c A
    → Δ ⊢c B
    → Δ ⊢c (A `→ B)
  ⊢c-∀ :
      Δ ,∙ ⊢c A
    → Δ ⊢c `∀ A
