module Implicit.Algo.Lookup where

open import Implicit.Language
open import Implicit.Algo.Syntax

private variable
  k : Fin m
  A A' B : Type m
  Σ : Context n m
  e : Term n m

infix 3 _εᶜ_
data _εᶜ_ : Fin m → Context n m → Set where
  ^∈-type  : (inA : k ε A)
           → k εᶜ (Context n m ∋⦂ (τ A))
           
  ^∈-term  : k εᶜ Σ
           → k εᶜ ([ e ]↝ Σ)

