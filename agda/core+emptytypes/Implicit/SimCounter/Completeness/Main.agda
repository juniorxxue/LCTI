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
complete (s-∀l s ic fd upC upD) fr bd'@(bd-c {j = j} {C = E} {A% = A%} bd grd)
  with ⟨ j' , upj ⟩ ← ↑tyʲ0-total j
  with ⟨ E' , upE ⟩ ← ↑ty0-total E
  with reg-S= r regA  ← s-sregulars s
  with ⟨ A%' , upA% ⟩ ← ↑ty0-total A%
  with regB ← ⊢t-⊢r (free-⊢t regA fr)
  = s-∀l (complete s (fr-S= fr) (bd-c (bound-weaken=0 bd regB upj upD upE)
         (≫-weaken= grd (▶Z regB) upC upA%))) case-𝕔
         (sfind-find fd (bound-weaken=0 bd' ⊢r-int (↑tyʲ-𝕔 upj) (↑ty-arr upC upD) (↑ty-arr upA% upE)))
         upA% upE (↑tyʲ-𝕔 upj)
complete (s-∀l s ic fd upC upD) fr bd'@(bd-i {j = j} {C = E} {A% = A%} bd grd)
  with ⟨ j' , upj ⟩ ← ↑tyʲ0-total j
  with ⟨ E' , upE ⟩ ← ↑ty0-total E
  with reg-S= r regA  ← s-sregulars s
  with ⟨ A%' , upA% ⟩ ← ↑ty0-total A%
  with regB ← ⊢t-⊢r (free-⊢t regA fr)
  = s-∀l (complete s (fr-S= fr) (bd-i (bound-weaken=0 bd regB upj upD upE)
         (≫-weaken= grd (▶Z regB) upC upA%))) case-𝕚
         (sfind-find fd (bound-weaken=0 bd' ⊢r-int (↑tyʲ-𝕚 upj) (↑ty-arr upC upD) (↑ty-arr upA% upE)))
         upA% upE (↑tyʲ-𝕚 upj)
complete (s-tapp s) fr (bd-t bd upj regT) = s-tapp (complete s (fr-S∙= fr regT) bd) upj
complete (s-svar-l x inΔ) fr (bd-∞ grd)
  with regA ← ⊢t-⊢r (free-⊢t (∋:=-⊢t x inΔ) fr)
  with refl ← ⊢r-≫-eq' regA grd
  = s-svar-l (free-sregular x fr) (free-∋:=' inΔ fr)
complete (s-svar-𝕚 x s) fr (bd-i bd grd) = s-svar-𝕚 (free-∋:=' x fr) (complete s fr (bd-i bd grd))
complete (s-svar-𝕔 x s) fr (bd-c bd grd) = s-svar-𝕔 (free-∋:=' x fr) (complete s fr (bd-c bd grd))
complete (s-svar-𝕥 x s) fr (bd-t bd upj regT) = s-svar-𝕥 (free-∋:=' x fr) (complete s fr (bd-t bd upj regT))


complete- (s-int regΔ) fr grd-int = s-int (free-sregular regΔ fr)
complete- (s-var-∙ regΔ inΔ) fr (grd-var= x) = s-svar-r (free-sregular regΔ fr) x
complete- (s-var-∙ regΔ inΔ) fr (grd-var∙ x) = s-var-∙ (free-sregular regΔ fr) x
complete- (s-arr₁ s s₁) fr (grd-arr grd grd₁) = s-arr₁ (complete s fr (bd-∞ grd)) (complete- s₁ fr grd₁)
complete- (s-∀ s) fr (grd-∀ grd) = s-∀ (complete- s (fr-S∙ fr) grd)
complete- (s-svar-r x inΔ) fr grd
  with regA ← ⊢t-⊢r (free-⊢t (∋:=-⊢t x inΔ) fr)
  with refl ← ⊢r-≫-eq' regA grd = s-svar-r (free-sregular x fr) (free-∋:=' inΔ fr)


complete0 : Γ ⋈ ⊨ 𝕟 # A ⌞ ≤⁺ ⌝ B
          → Bound (Γ ⋈) (⟨ 𝕟 , B ⟩) (⟨ j , C ⟩) 
          → Γ ⋈ ⊢ j # A ⌞ ≤⁺ ⌝ C
complete0 ⊢e bd = complete ⊢e fr-⋈ bd
