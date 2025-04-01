module Implicit.Interm2Decl.Main where

open import Implicit.Language.All
open import Implicit.Decl.All renaming (_⊢_#_⌞_⌝_ to _⊢d_#_⌞_⌝_)
open import Implicit.Interm.All renaming (_⊢_#_⌞_⌝_ to _⊢i_#_⌞_⌝_)

postulate

  sd-strengthen=0 : Γ ,= T ⊢d j # A' ⌞ ≤ ⌝ B'
                  → ↑ty0 A ⇘ A'
                  → ↑ty0 B ⇘ B'
                  → Γ ⊢d j # A ⌞ ≤ ⌝ B

sound : Γ ⊢i j # A ⌞ ≤ ⌝ B
      → Γ ≫ A ⇘ A%
      → Γ ≫ B ⇘ B%
      → Γ ⊢d j # A% ⌞ ≤ ⌝ B%
sound (s-refl regΔ cloA grd) grd1 grd2 = {!!}
sound (s-int regΔ) grd1 grd2 = {!!}
sound (s-var-∙ regΔ inΔ) grd1 grd2 = {!!}
sound (s-arr₁ s s₁) grd1 grd2 = {!!}
sound (s-arr₂ s s₁) grd1 grd2 = {!!}
sound (s-arr₃ cloA grd s) grd1 grd2 = {!!}
sound (s-∀ s) grd1 grd2 = {!!}
sound (s-∀l s ic fd upC upD) (grd-∀ grd1) (grd-arr grd2 grd3) = s-∀l {!!} (sd-strengthen=0 (sound s {!!} {!!}) {!!} {!!}) ic {!!}
sound (s-svar-l x inΔ) grd1 grd2 = {!!}
sound (s-svar-r x inΔ) grd1 grd2 = {!!}
