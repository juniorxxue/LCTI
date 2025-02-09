module Implicit.Interm.Properties.Subtyping where

open import Implicit.Language.All
open import Implicit.Interm.Base

⊢sub' : Γ ⊢ Z # e ⦂ B
      → Γ ⊢ j # B ≤ A
      → Γ ⊢ j # e ⦂ A
⊢sub' {j = Z} ⊢e (s-refl cloΣ cloA) = ⊢e
⊢sub' {j = ∞} ⊢e s = ⊢sub ⊢e s nz-∞
⊢sub' {j = 𝕚 j} ⊢e s = ⊢sub ⊢e s nz-I
⊢sub' {j = 𝕔 j} ⊢e s = ⊢sub ⊢e s nz-C

s-refl-∞ : Closed Γ
         → Γ ⊢c A
         → Γ ⊢ ∞ # A ≤ A
s-refl-∞ cloΓ ⊢c-int = s-int cloΓ
s-refl-∞ cloΓ (⊢c-var-∙ inΓ) = s-var-∙ cloΓ inΓ
s-refl-∞ cloΓ (⊢c-var-= inΓ) = s-var-= cloΓ inΓ
s-refl-∞ cloΓ (⊢c-arr cloA cloA₁) = s-arr₁ (s-refl-∞ cloΓ cloA) (s-refl-∞ cloΓ cloA₁)
s-refl-∞ cloΓ (⊢c-∀ cloA) = s-∀ (s-refl-∞ (clo-S∙ cloΓ) cloA)
