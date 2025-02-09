module Implicit.Algo.Lookup where

open import Implicit.Language.All
open import Implicit.Algo.Syntax

infix 3 _εᶜ_
data _εᶜ_ : Fin m → Context n m → Set where
  ^∈-type  : (inA : k ε A)
           → k εᶜ (Context n m ∋⦂ (τ A))

  ^∈-term  : k εᶜ Σ
           → k εᶜ ([ e ]↝ Σ)
