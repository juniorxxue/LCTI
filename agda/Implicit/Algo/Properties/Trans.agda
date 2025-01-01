module Implicit.Algo.Properties.Trans where

-- not exactly like transitivity in classic subtyping
-- since we don't subsume it
-- it only describes the relation between *updates contexts*, used in subsumption lemma in ⊢sub case

open import Implicit.Language
open import Implicit.Algo.Base

s-trans : Γ ⊢ A₁ ⌞ ≤ ⌝ Σ ⊣ Δ ↪ A₂
        → Σ ≊ Σ'
        → Γ ⊢ A₂ ⌞ ≤ ⌝ Σ' ⊣ Ψ ↪ A₃
        → Γ ⊢ A₁ ⌞ ≤ ⌝ Σ' ⊣ Ψ ↪ A₃
s-trans s1 newΣ s2 = {!!}        
