module Implicit.Algo.Properties.SubIrrelevance where

-- the irrelevance in altering (unsolving unrelated solutions in) subtyping environments

open import Implicit.Language.All
open import Implicit.Algo.Base
open import Implicit.Algo.Properties.Extension


postulate
  s-irrev-⊆ : Γ ⊢ A ≤⁺ Σ ⊣ Γ ↪ B
            → Γ ⊆ Δ
            → Δ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B
