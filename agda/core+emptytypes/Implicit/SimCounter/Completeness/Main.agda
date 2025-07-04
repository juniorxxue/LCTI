module Implicit.SimCounter.Completeness.Main where

open import Implicit.Language.All
open import Implicit.AuxLemmas
open import Implicit.SimCounter.Typing
open import Implicit.SimCounter.Subtyping
open import Implicit.SimCounter.Interm
open import Implicit.SimCounter.Completeness.Aux
open import Implicit.SimCounter.RegularNew

complete : Γ ⊨ 𝕟 # A ≤ B
         → Free Γ Δ
         → Bound Δ (⟨ 𝕟 , B ⟩) (⟨ j , C ⟩)
         → Δ ⊢ j # A ⌞ ≤⁺ ⌝ C

complete- : Γ ⊨ ∞ # B ≤ A
         → Free Γ Δ
         → Δ ≫ B ⇘ C
         → Δ ⊢ ∞ # C ⌞ ≤⁻ ⌝ A

complete (s-refl regΔ cloA) fr bd = {!!}
complete (s-int regΔ) fr bd = {!!}
complete (s-var-∙ regΔ inΔ) fr bd = {!!}
complete (s-arr₁ s s₁) fr bd = {!!}
complete (s-arr₂ s s₁) fr bd = {!!}
complete (s-arr₃ regA s) fr bd = {!!}
complete (s-∀ s) fr bd = {!!}
complete (s-∀l regB st s ic fd) fr bd = {!!}
complete (s-∀l-no-appear regB st s ic fd) fr bd = {!!}
complete (s-∀l-X regB st s ic fd inΔ) fr bd = {!!}
complete (s-∀l-no-appear-X regB st s ic fd inΔ) fr bd = {!!}
complete (s-tapp s) fr (bd-t bd upj regT) = s-tapp (complete s (fr-S∙= fr regT) bd) upj

complete- (s-int regΔ) fr grd-int = s-int {!!}
complete- (s-var-∙ regΔ inΔ) fr grd = {!!}
complete- (s-arr₁ s s₁) fr grd = {!!}
complete- (s-∀ s) fr grd = {!!}
complete- (s-∀l-no-appear regB st s ic fd) fr grd = {!!}
