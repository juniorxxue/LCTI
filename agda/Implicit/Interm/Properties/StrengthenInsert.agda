module Implicit.Interm.Properties.StrengthenInsert where

open import Implicit.Language.All
open import Implicit.Interm.Base

s-strengthen= : Γ' ⊢ j # A' ⌞ ≤ ⌝ B'
              → Γ ▶ k ,= T ⇘ Γ'
              → A ↑ty k ⇘ A'
              → B ↑ty k ⇘ B'
              → Γ ⊢ j # A ⌞ ≤ ⌝ B
s-strengthen= (s-refl regΔ cloA grd) newΓ upA upB = {!!}
s-strengthen= (s-int regΔ) newΓ upA upB = {!!}
s-strengthen= (s-var-∙ regΔ inΔ) newΓ upA upB = {!!}
s-strengthen= (s-arr₁ s s₁) newΓ upA upB = {!!}
s-strengthen= (s-arr₂ s s₁) newΓ upA upB = {!!}
s-strengthen= (s-arr₃ cloA grd s) newΓ upA upB = {!!}
s-strengthen= (s-∀ s) newΓ upA upB = {!!}
s-strengthen= (s-∀l s ic fd upC upD) newΓ (↑ty-∀ upA) (↑ty-arr upB upB₁)
  = s-∀l (s-strengthen= s (▶S= newΓ {!!} {!!}) {!!} {!!}) {!!} {!!} {!!} {!!}
s-strengthen= (s-svar-l x inΔ) newΓ upA upB = {!!}
s-strengthen= (s-svar-r x inΔ) newΓ upA upB = {!!}
