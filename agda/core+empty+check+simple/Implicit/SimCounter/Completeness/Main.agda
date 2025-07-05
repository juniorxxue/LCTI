module Implicit.SimCounter.Completeness.Main where

open import Implicit.Language.All
open import Implicit.AuxLemmas
open import Implicit.SimCounter.Typing
open import Implicit.SimCounter.Subtyping2
open import Implicit.Interm.All
open import Implicit.SimCounter.Completeness.Aux

complete : Γ ⊨ 𝕟 # A ⌞ ≤⁺ ⌝ B
         → Free Γ Δ
         → Bound Δ (⟨ 𝕟 , B ⟩) (⟨ j , C ⟩)
         → Δ ⊢ j # A ⌞ ≤⁺ ⌝ C

complete- : Γ ⊨ ∞ # A ⌞ ≤⁻ ⌝ B
         → Free Γ Δ
         → Δ ≫ A ⇘ C
         → Δ ⊢ ∞ # C ⌞ ≤⁻ ⌝ B

complete (s-refl regΔ cloA grd) fr (bd-z grd₁) = s-refl (free-sregular regΔ fr) (free-⊢c cloA fr) (free-≫ regΔ grd fr grd₁)
complete (s-int regΔ) fr (bd-∞ grd-int) = s-int (free-sregular regΔ fr)
complete (s-var-∙ regΔ inΔ) fr (bd-∞ (grd-var= x)) = s-svar-l (free-sregular regΔ fr) x
complete (s-var-∙ regΔ inΔ) fr (bd-∞ (grd-var∙ x)) = s-var-∙ (free-sregular regΔ fr) x
complete (s-arr₁ s s₁) fr (bd-∞ (grd-arr grd grd₁)) = s-arr₁ (complete- s fr grd) (complete s₁ fr (bd-∞ grd₁))
complete (s-arr₂ s s₁) fr (bd-i bd grd) = s-arr₂ (complete- s fr grd) (complete s₁ fr bd)
complete (s-arr₃ cloA grd s) fr (bd-c bd grd₁) = s-arr₃ (free-⊢c cloA fr) (free-≫ (s-sregulars s) grd fr grd₁) (complete s fr bd)
complete (s-∀ s) fr (bd-∞ (grd-∀ grd)) = s-∀ (complete s (fr-S∙ fr) (bd-∞ grd))
complete (s-∀l s ic fd upC upD) fr (bd-c bd grd) = {!!}
complete (s-∀l s ic fd upC upD) fr (bd-i bd grd) = {!!}
complete (s-tapp s) fr (bd-t bd upj regT) = s-tapp (complete s (fr-S∙= fr regT) bd) upj
complete (s-svar-l x inΔ) fr (bd-∞ grd)
  with regA ← ⊢t-⊢r (free-⊢t (∋:=-⊢t x inΔ) fr)
  with refl ← ⊢r-≫-eq' regA grd
  = s-svar-l (free-sregular x fr) (free-∋:=' inΔ fr)
complete (s-svar-𝕚 x s) fr (bd-i bd grd) = s-svar-𝕚 (free-∋:=' x fr) (complete s fr (bd-i bd grd))
complete (s-svar-𝕔 x s) fr (bd-c bd grd) = s-svar-𝕔 (free-∋:=' x fr) (complete s fr (bd-c bd grd))
complete (s-svar-𝕥 x s) fr (bd-t bd upj regT) = s-svar-𝕥 (free-∋:=' x fr) (complete s fr (bd-t bd upj regT))
