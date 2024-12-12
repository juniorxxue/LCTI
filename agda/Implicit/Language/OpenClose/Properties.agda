module Implicit.Language.OpenClose.Properties where

open import Implicit.Language.Base
open import Implicit.Language.OpenClose.Base

private variable
  Γ : Env n m
  A B : Type m

postulate
  ⊢c-weaken0 : Γ , B ⊢c A
             → Γ ⊢c A

  ⊢c-strengthen0 : Γ ⊢c A
                 → Γ , B ⊢c A

  
  
