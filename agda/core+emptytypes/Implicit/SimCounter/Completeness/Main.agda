module Implicit.SimCounter.Completeness.Main where

open import Implicit.Language.All
open import Implicit.AuxLemmas
open import Implicit.SimCounter.Typing
open import Implicit.SimCounter.Subtyping
open import Implicit.SimCounter.Interm
open import Implicit.SimCounter.Completeness.Aux

complete : Γ ⊨ 𝕟 # A ≤ B
         → Free Γ Δ
         → Bound Δ (⟨ 𝕟 , B ⟩) (⟨ j , C ⟩)
         → Δ ⊢ j # A ⌞ ≤⁺ ⌝ C

complete- : Γ ⊨ ∞ # B ≤ A
         → Free Γ Δ
         → Δ ≫ B ⇘ C
         → Δ ⊢ ∞ # C ⌞ ≤⁻ ⌝ A

complete (s-refl regΔ cloA) fr (bd-z grd) = s-refl {!!} {!!} grd
complete (s-int regΔ) fr (bd-∞ grd-int) = s-int {!!}
complete (s-var-∙ regΔ inΔ) fr (bd-z grd) = {!!}
complete (s-var-∙ regΔ inΔ) fr (bd-∞ grd) = {!!}
complete (s-arr₁ s s₁) fr (bd-∞ (grd-arr grd grd₁)) = s-arr₁ (complete- s fr grd) (complete s₁ fr (bd-∞ grd₁))
complete (s-arr₂ s s₁) fr bd = {!!}
complete (s-arr₃ regA s) fr bd = {!!}
complete (s-∀ s) fr bd = {!!}
complete (s-∀l regB st s ic fd) fr (bd-c bd grd) = s-∀l (complete s fr (bd-c bd grd)) case-𝕔 {!!} {!!} st
complete (s-∀l regB st s ic fd) fr (bd-i bd grd) = {!!}
complete (s-∀l-no-appear regB st s ic fd) fr bd = {!!}
complete (s-tapp s) fr (bd-t bd upj regT) = s-tapp (complete s (fr-S∙= fr regT) bd) upj

complete- (s-int regΔ) fr grd = {!!}
complete- (s-var-∙ regΔ inΔ) fr grd = {!!}
complete- (s-arr₁ s s₁) fr grd = {!!}
complete- (s-∀ s) fr grd = {!!}
complete- (s-∀l-no-appear regB st s ic fd) fr grd = {!!}
