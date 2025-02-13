module Implicit.CompleteDeclInterm where

open import Implicit.Language.All hiding (_≤_)
open import Implicit.Decl.All renaming (_⊢_#_⦂_ to _⊢d_#_⦂_; _⊢_#_≤_ to _⊢d_#_≤_; s-refl-∞ to sd-refl-∞)
open import Implicit.Interm.All renaming (_⊢_#_⦂_ to _⊢i_#_⦂_; _⊢_#_≤_ to _⊢i_#_≤_)

complete-s : Γ ⊢d j # A ≤ B
           → Γ ≫ A ⇘ A%
           → Γ ≫ B ⇘ B%
           → Γ ⊢i j # A% ≤ B%
complete-s (s-refl cloΓ cloA) grA grB = {!!}
complete-s (s-int cloΓ) grA grB = {!!}
complete-s (s-var-∙ cloΓ inΓ) grA grB = {!!}
complete-s (s-arr₁ s s₁) grA grB = {!!}
complete-s (s-arr₂ s s₁) grA grB = {!!}
complete-s (s-arr₃ cloA s) grA grB = {!!}
complete-s (s-∀ s) grA grB = {!!}
complete-s (s-∀l x s ic fd) (grd-∀ grA) (grd-arr grB grB₁) =
  s-∀l {!complete-s s ? ?!} ic {!!} {!!} {!!}
