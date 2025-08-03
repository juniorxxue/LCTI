module Implicit.Language.EnvOps.Strengthen.Misc where

open import Implicit.Language.Base
open import Implicit.Language.Shift.All
open import Implicit.Language.Lookup.All
open import Implicit.Language.EnvOps.Strengthen.Base
open import Implicit.Language.EnvOps.Strengthen.Lookup


-- ⊢r-strengthen∙0 : Γ ,∙ ⊢r A'
--                     → ↑ty0 A ⇘ A'
--                     → Γ ⊢r A
-- ⊢r-strengthen∙0 regA upA = ⊢r-strengthen= regA ? upA
