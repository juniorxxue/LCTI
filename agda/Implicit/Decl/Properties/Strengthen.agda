module Implicit.Decl.Properties.Strengthen where

open import Implicit.Language
open import Implicit.Decl.Base

private variable
  Γ : Env n m
  A B A' B' C T : Type m
  j : Counter
  e : Term n m

postulate
  
  strengthen-0 : Γ , A ⊢ j # ↑tm0 e ⦂ B
               → Γ ⊢ j # e ⦂ B

  s-strengthen,0 : Γ , A ⊢ j # B ≤ C
                 → Γ ⊢ j # B ≤ C
