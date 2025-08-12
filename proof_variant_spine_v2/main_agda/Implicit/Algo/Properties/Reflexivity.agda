module Implicit.Algo.Properties.Reflexivity where

open import Implicit.Language.All
open import Implicit.Algo.Base


s-refl : SRegular Γ
       → Γ ⊢r A
       → Γ ⊢ A ⌞ ≤ ⌝ A ⊣ Γ
s-refl regΓ ⊢r-int = s-int regΓ
s-refl regΓ (⊢r-var-∙ inΓ) = s-var-∙ regΓ inΓ
s-refl regΓ (⊢r-arr regA regA₁) = s-arr (s-refl regΓ regA) (s-refl regΓ regA₁)
s-refl regΓ (⊢r-∀ regA) = s-∀ (s-refl (reg-S∙ regΓ) regA)
