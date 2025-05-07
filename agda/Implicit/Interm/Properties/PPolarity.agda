module Implicit.Interm.Properties.PPolarity where

open import Implicit.Language.All
open import Implicit.Interm.Base
open import Implicit.Interm.Properties.PRegularity

postulate
  s+-polarity : Γ ⊢ j # A ⌞ ≤⁺ ⌝ B
              → Γ ⊢r B

postulate
  s--polarity : Γ ⊢ j # A ⌞ ≤⁻ ⌝ B
              → Γ ⊢r A

postulate
  t-⊢r : Γ ⊢ j # e ⦂ A
       → Γ ⊢r A

postulate
  s-⊢c-l : Γ ⊢ j # A ⌞ ≤ ⌝ B
          → Γ ⊢c A

postulate
  s-⊢c-r : Γ ⊢ j # A ⌞ ≤ ⌝ B
          → Γ ⊢c B

