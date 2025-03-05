module Implicit.Language.OpenClose.Base where

open import Implicit.Language.Base
open import Implicit.Language.Lookup.Base

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
