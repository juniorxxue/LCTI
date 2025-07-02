module Implicit.SimCounter.Completeness.Sound where

open import Implicit.Language.All
open import Implicit.AuxLemmas
open import Implicit.SimCounter.Typing
open import Implicit.SimCounter.Subtyping2
open import Implicit.Interm.All
open import Implicit.SimCounter.Completeness.Aux


sound : Δ ⊢ j # A ⌞ ≤⁺ ⌝ C
       → Free Γ Δ
       → Bound Γ (⟨ 𝕟 , B ⟩) (⟨ j , C ⟩)
       → Γ ⊨ 𝕟 # A ⌞ ≤⁺ ⌝ B

sound- : Δ ⊢ ∞ # C ⌞ ≤⁻ ⌝ B
        → Free Γ Δ
        → Γ ≫ A ⇘ C
        → Γ ⊨ ∞ # A ⌞ ≤⁻ ⌝ B
sound- (s-int regΔ) fr grd-int = s-int {!!}
sound- (s-int regΔ) fr (grd-var= x) = {!!}
sound- (s-var-∙ regΔ inΔ) fr grd = {!!}
sound- (s-arr₁ s s₁) fr grd = {!!}
sound- (s-∀ s) fr grd = {!!}
sound- (s-svar-r x inΔ) fr grd = {!!}
