module Implicit.Language.OpenClose.Subst where

open import Implicit.Language.Base
open import Implicit.Language.Lookup
open import Implicit.Language.Shift
open import Implicit.Language.Subst
open import Implicit.Language.OpenClose.Base

postulate

  ⊢c-subst0 : Δ ,= T ⊢c A
           → ⟦ T ⟧ A ⇘ A*
           → Δ ⊢c A*
