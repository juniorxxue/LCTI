module Implicit.Decl.Properties.Strengthen where

open import Implicit.Language
open import Implicit.Decl.Base

postulate
  
  strengthen-0 : ∀ {Γ : Env n m} {j A B e}
    → Γ , A ⊢ j # ↑tm0 e ⦂ B
    → Γ ⊢ j # e ⦂ B

  s-strengthen-tm-0 : ∀ {Γ : Env n m} {A B C j}
    → Γ , A ⊢ j # B ≤ C
    → Γ ⊢ j # B ≤ C
