module Implicit.Decl2Interm.Main where

open import Implicit.Language.All
open import Implicit.Decl.All renaming (_⊢_#_⌞_⌝_ to _⊢d_#_⌞_⌝_)
open import Implicit.Interm.All renaming (_⊢_#_⌞_⌝_ to _⊢i_#_⌞_⌝_)

complete : Γ ⊢d j # A% ⌞ ≤ ⌝ B%
         → Γ ≫ A ⇘ A%
         → Γ ≫ B ⇘ B% -- we cannot replace it freely, need to be careful
         → Γ ⊢i j # A ⌞ ≤ ⌝ B
complete (s-refl regΔ cloA) grd1 grd2 = {!!}
complete (s-int regΔ) grd1 grd2 = {!!}
complete (s-var-∙ regΔ inΔ) grd1 grd2 = {!!}
complete (s-arr₁ s s₁) grd1 grd2 = {!!}
complete (s-arr₂ s s₁) grd1 grd2 = {!!}
complete (s-arr₃ s) grd1 grd2 = {!!}
complete (s-∀ s) grd1 grd2 = {!!}
complete (s-∀l grd s ic fd upC upD upj) (grd-var= x) (grd-var= x₁) = {!!}
complete (s-∀l grd s ic fd upC upD upj) (grd-var= x) (grd-arr grd2 grd3) = {!!}
complete (s-∀l grd s ic fd upC upD upj) (grd-∀ grd1) grd2 = {!!}
complete (s-tapp x s upC) grd1 grd2 = {!!}
