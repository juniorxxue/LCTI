module Implicit.Interm.Properties.Access where

open import Implicit.Language.All
open import Implicit.AuxLemmas
open import Implicit.Interm.Base
open import Implicit.Interm.Properties.Regularity

data LessEq : HitMis m → HitMis m → Set where
  le-z1 : LessEq (hit H₁) (hit H₂)
  le-z2 : LessEq (hit H₁) (mis H₂)
  le-z3 : LessEq ∅ ∅
  le-s : LessEq H₁ H₂
       → LessEq (mis H₁) (mis H₂)

le-all-miss : ∀ {m} → LessEq (mkMis {m}) (mkMis {m})
le-all-miss {m = zero} = le-z3
le-all-miss {m = suc m} = le-s le-all-miss

le-∋:= : Γ ∋ X := A
       → A 𝕗𝕧 H
       → LessEq (mkHit X) H

≫-bloc : Γ ≫ A ⇘ B
       → A 𝕗𝕧 H₁
       → B 𝕗𝕧 H₂
       → LessEq H₁ H₂
≫-bloc grd-int fv-Int fv-Int = le-all-miss
≫-bloc (grd-var= x) fv-var fB = {!!}
≫-bloc (grd-var∙ x) fA fB = {!!}
≫-bloc (grd-arr grd grd₁) fA fB = {!!}
≫-bloc (grd-∀ grd) fA fB = {!!}

s-bloc : Γ ⊢ j # A ⌞ ≤⁺ ⌝ B
       → A 𝕗𝕧 H₁
       → B 𝕗𝕧 H₂
       → LessEq H₁ H₂
s-bloc (s-refl regΔ cloA grd) fA fB = {!!}
s-bloc (s-int regΔ) fA fB = {!!}
s-bloc (s-var-∙ regΔ inΔ) fA fB = {!!}
s-bloc (s-arr₁ s s₁) fA fB = {!!}
s-bloc (s-arr₂ s s₁) fA fB = {!!}
s-bloc (s-arr₃ cloA grd s) fA fB = {!!}
s-bloc (s-∀ s) fA fB = {!!}
s-bloc (s-∀l s ic fd upC upD upj) (fv-∀-h fA) fB = {!s-bloc s fA ?!}
s-bloc (s-∀l s ic fd upC upD upj) (fv-∀-m fA) fB = ⊥-elim _ -- not miss
s-bloc (s-∀l-no-appear s ic fd upC upD upj) fA fB = {!!}
s-bloc (s-tapp s upj) fA fB = {!!}
s-bloc (s-svar-l x inΔ) fA fB = {!!}
s-bloc (s-svar-𝕚 x s) fA fB = {!!}
s-bloc (s-svar-𝕔 x s) fA fB = {!!}
s-bloc (s-svar-𝕥 x s) fA fB = {!!}
