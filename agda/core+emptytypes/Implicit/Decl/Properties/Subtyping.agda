module Implicit.Decl.Properties.Subtyping where

open import Implicit.Language.All
open import Implicit.Decl.Base

⊢sub' : Γ ⊢ Z # e ⦂ B
      → Γ ⊢ j # B ≤ A
      → Γ ⊢ j # e ⦂ A
⊢sub' {j = Z} ⊢e (s-refl cloΣ cloA) = ⊢e
⊢sub' {j = ∞} ⊢e s = ⊢sub ⊢e s nz-∞
⊢sub' {j = 𝕚 j} ⊢e s = ⊢sub ⊢e s nz-I
⊢sub' {j = 𝕔 j} ⊢e s = ⊢sub ⊢e s nz-C

s-refl-∞ : Norm Γ
         → Γ ⊢n A
         → Γ ⊢ ∞ # A ≤ A
s-refl-∞ norΓ ⊢n-int = s-int norΓ
s-refl-∞ norΓ (⊢n-var-∙ inΓ) = s-var-∙ norΓ inΓ
s-refl-∞ norΓ (⊢n-arr norA norA₁) = s-arr₁ (s-refl-∞ norΓ norA) (s-refl-∞ norΓ norA₁)
s-refl-∞ norΓ (⊢n-∀ norA) = s-∀ (s-refl-∞ (nom-S∙ norΓ) norA)
