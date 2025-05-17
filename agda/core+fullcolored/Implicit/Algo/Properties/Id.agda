module Implicit.Algo.Properties.Id where

open import Implicit.Language.All
open import Implicit.Algo.Base
open import Implicit.Algo.Properties.Subst

postulate
  ⊢id0 : Γ ⊢ `τ B ⇒ e ⇒ A
     → B ≡ A

  s-id0 : Γ ⊢ A ≤⁺ `τ B ⊣ Γ' ↪ C
      → B ≡ C
