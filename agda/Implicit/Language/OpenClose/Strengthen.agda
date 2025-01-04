module Implicit.Language.OpenClose.Strengthen where

open import Implicit.Language.Base
open import Implicit.Language.Lookup
open import Implicit.Language.Shift
open import Implicit.Language.Subst
open import Implicit.Language.OpenClose.Base


postulate
  ⊢c-strengthen,0 : Γ , B ⊢c A
                  → Γ ⊢c A

  ⊢c-strengthen^0 : Γ ,^ ⊢c A'
                  → ↑ty0 A ⇘ A'
                  → Γ ⊢c A

  ⊢c-strengthen=0 : Γ ,= T ⊢c A'
                  → ↑ty0 A ⇘ A'
                  → Γ ⊢c A

  ⊢c-strengthen∙0 : Γ ,∙ ⊢c A'
                  → ↑ty0 A ⇘ A'
                  → Γ ⊢c A
