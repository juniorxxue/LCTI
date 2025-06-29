module Implicit.SimCounter.Completeness.Main where

open import Implicit.Language.All
open import Implicit.AuxLemmas
open import Implicit.SimCounter.Typing
open import Implicit.SimCounter.Subtyping2
open import Implicit.SimCounter.Completeness.Interm
open import Implicit.SimCounter.Completeness.Aux

complete : Γ ⊨ 𝕟 # A ⌞ ≤⁺ ⌝ B
         → Bound Γ (⟨ 𝕟 , B ⟩) (⟨ j , C ⟩)
         → Free Γ Δ
         → Δ ≫ C ⇘ D
         → Δ ⊢ j # A ⌞ ≤⁺ ⌝ D

complete- : Γ ⊨ ∞ # A ⌞ ≤⁻ ⌝ B
         → Free Γ Δ
         → Δ ≫ A ⇘ C
         → Δ ⊢ ∞ # C ⌞ ≤⁻ ⌝ B

complete (s-refl regΔ cloA grd₁) bd-z fr grd = s-refl (free-sregulars regΔ fr) {!!} {!!}
complete (s-int regΔ) bd-∞ fr grd-int = s-int (free-sregulars regΔ fr)
complete (s-var-∙ regΔ inΔ) bd-∞ fr (grd-var= x) = s-svar-l (free-sregulars regΔ fr) x
complete (s-var-∙ regΔ inΔ) bd-∞ fr (grd-var∙ x) = s-var-∙ (free-sregulars regΔ fr) x
complete (s-arr₁ s s₁) bd-∞ fr (grd-arr grd grd₁) = s-arr₁ (complete- s fr grd) (complete s₁ bd-∞ fr grd₁)
complete (s-arr₂ s s₁) (bd-i bd) fr (grd-arr grd grd₁) = s-arr₂ (complete- s fr grd) (complete s₁ bd fr grd₁)
complete (s-arr₃ cloA grd₁ s) (bd-c bd) fr (grd-arr grd grd₂) = s-arr₃ {!!} {!!} (complete s bd fr grd₂)
complete (s-∀ s) bd-∞ fr (grd-∀ grd) = s-∀ (complete s bd-∞ (fr-S∙ fr) grd)
complete (s-∀l s ic fd upC upD) (bd-c bd) fr (grd-arr grd grd₁) = s-∀l (complete s {!!} (fr-S= fr) {!!}) case-𝕔 {!!} {!!} {!!} {!!}
complete (s-∀l s ic fd upC upD) (bd-i bd) fr grd = {!!}
complete (s-tapp s) (bd-t bd x x₁ x₂ x₃) fr (grd-∀ grd) = s-tapp (complete s bd (fr-S∙= fr (free-⊢t x fr)) {!!}) x₃
complete (s-svar-l inΓ inΔ) bd-∞ fr grd = s-svar-l (free-sregulars inΓ fr) {!!}
complete (s-svar-𝕚 inΓ s) (bd-i bd) fr (grd-arr grd grd₁) = s-svar-𝕚 (free-∋:=' inΓ fr) (complete s (bd-i bd) fr (grd-arr grd grd₁))
complete (s-svar-𝕔 inΓ s) (bd-c bd) fr (grd-arr grd grd₁) = s-svar-𝕔 (free-∋:=' inΓ fr) (complete s (bd-c bd) fr (grd-arr grd grd₁))
complete (s-svar-𝕥 inΓ s) (bd-t bd x x₁ x₂ x₃) fr (grd-∀ grd) = s-svar-𝕥 (free-∋:=' inΓ fr) (complete s (bd-t bd x x₁ x₂ x₃) fr (grd-∀ grd))

complete- (s-int regΔ) fr grd-int = s-int (free-sregulars regΔ fr)
complete- (s-var-∙ regΔ inΔ) fr (grd-var= x) = s-svar-r (free-sregulars regΔ fr) x
complete- (s-var-∙ regΔ inΔ) fr (grd-var∙ x) = s-var-∙ (free-sregulars regΔ fr) x
complete- (s-arr₁ s s₁) fr (grd-arr grd grd₁) = s-arr₁ (complete s bd-∞ fr grd) (complete- s₁ fr grd₁)
complete- (s-∀ s) fr (grd-∀ grd) = s-∀ (complete- s (fr-S∙ fr) grd)
complete- (s-svar-r x inΔ) fr grd = s-svar-r (free-sregulars x fr) {!!}


complete0 : Γ ⋈ ⊨ 𝕟 # A ⌞ ≤⁺ ⌝ B
          → Bound (Γ ⋈) (⟨ 𝕟 , B ⟩) (⟨ j , C ⟩)
          → Γ ⋈ ⊢ j # A ⌞ ≤⁺ ⌝ C
complete0 ⊢e bd = complete ⊢e bd fr-⋈ {!!}
