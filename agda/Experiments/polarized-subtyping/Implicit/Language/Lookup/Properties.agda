module Implicit.Language.Lookup.Properties where

open import Implicit.Language.Base
open import Implicit.Language.Lookup.Base

private variable
  Γ : Env n m
  k : Fin m
  x : Fin n
  A : Type m
  

postulate

  -- remove a term binding from the environment
  -- the solution is expected to hold, with the same type
  ∋,-weaken-sol :
      (Γ /,/ k) ∋ x := A
    → Γ ∋ x := A




