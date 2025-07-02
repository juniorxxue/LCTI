module Implicit.SimCounter.Completeness.Sound where

open import Implicit.Language.All
open import Implicit.AuxLemmas
open import Implicit.SimCounter.Typing
open import Implicit.SimCounter.Subtyping
open import Implicit.SimCounter.IntermEla
open import Implicit.SimCounter.Completeness.Aux

free-∋∙' : Δ ∋ X := A
         → Free Γ Δ
         → Γ ∋∙ X
free-∋∙' (Z up) (fr-S∙= fr x) = Z
free-∋∙' (S∙ inΔ up) (fr-S∙ fr) = S∙ (free-∋∙' inΔ fr)
free-∋∙' (S= inΔ up) (fr-S∙= fr x) = S∙ (free-∋∙' inΔ fr)


sound : Δ ⊢ j # A ⌞ ≤⁺ ⌝ B ↡ B✦
       → Free Γ Δ
       → Γ ⊨ 𝕟 # A ≤ B✦
sound (s-refl regΔ cloA grd) fr = {!!}
sound (s-int regΔ) fr = {!!}
sound (s-var-∙ regΔ inΔ) fr = {!!}
sound (s-arr₁ s s₁) fr = {!!}
sound (s-arr₂ s s₁) fr = {!!}
sound (s-arr₃ cloA grd s) fr = {!!}
sound (s-∀ s) fr = {!!}
sound (s-∀l s ic fd upj st) fr = {!!}
sound (s-∀l-no-appear s ic fd upj st) fr = {!!}
sound (s-tapp s upj) fr = {!!}
sound (s-svar-l x inΔ) fr = {!!}
sound (s-svar-𝕚 x s) fr = {!!}
sound (s-svar-𝕔 x s) fr = {!!}
sound (s-svar-𝕥 x s) fr = {!!}
