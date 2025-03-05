module Implicit.Language.Extension.Properties where

open import Implicit.Language.Base
open import Implicit.Language.Lookup.All

open import Implicit.Language.EnvOps.Base
open import Implicit.Language.Regular.Base

open import Implicit.Language.Extension.Base

----------------------------------------------------------------------
--+                         refl and trans                         +--
----------------------------------------------------------------------

⊆-refl : SRegular Γ
       → Γ ⊆ Γ
⊆-refl (reg-Z regΓ) = mark regΓ
⊆-refl (reg-S∙ senv) = uvar (⊆-refl senv)
⊆-refl (reg-S^ senv) = evar (⊆-refl senv)
⊆-refl (reg-S= senv regA) = svar (⊆-refl senv) regA
