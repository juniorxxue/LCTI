module Implicit.Decl.Properties.Subtyping where

open import Implicit.Language
open import Implicit.Decl.Base

⊢sub' : ∀ {Γ : Env n m} {e A B j}
  → Γ ⊢ Z # e ⦂ B
  → Γ ⊢ j # B ≤ A
  → Γ ⊢ j # e ⦂ A
⊢sub' {j = Z} ⊢e s-refl = ⊢e
⊢sub' {j = ∞} ⊢e s = ⊢sub ⊢e s nz-∞
⊢sub' {j = 𝕚 j} ⊢e s = ⊢sub ⊢e s nz-I
⊢sub' {j = 𝕔 j} ⊢e s = ⊢sub ⊢e s nz-C

s-refl-∞ : ∀ {Γ : Env n m} {A}
  → Γ ⊢ ∞ # A ≤ A
s-refl-∞ {A = Int} = s-int
s-refl-∞ {A = ‶ X} = s-var
s-refl-∞ {A = A `→ A₁} = s-arr₁ s-refl-∞ s-refl-∞
s-refl-∞ {A = `∀ A} = s-∀ s-refl-∞
