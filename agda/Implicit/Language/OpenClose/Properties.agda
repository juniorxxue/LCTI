module Implicit.Language.OpenClose.Properties where

open import Implicit.Language.Base
open import Implicit.Language.OpenClose.Base

postulate
  ⊢c-weaken0 : Γ , B ⊢c A
             → Γ ⊢c A

  ⊢c-strengthen0 : Γ ⊢c A
                 → Γ , B ⊢c A

  
  
