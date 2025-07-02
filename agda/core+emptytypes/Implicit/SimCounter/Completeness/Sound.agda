module Implicit.SimCounter.Completeness.Sound where

open import Implicit.Language.All
open import Implicit.AuxLemmas
open import Implicit.SimCounter.Typing
open import Implicit.SimCounter.Subtyping
open import Implicit.SimCounter.IntermEla
open import Implicit.SimCounter.Completeness.Aux
open import Implicit.SimCounter.RegularNew

free-∋∙' : Δ ∋ X := A
         → Free Γ Δ
         → Γ ∋∙ X
free-∋∙' (Z up) (fr-S∙= fr x) = Z
free-∋∙' (S∙ inΔ up) (fr-S∙ fr) = S∙ (free-∋∙' inΔ fr)
free-∋∙' (S= inΔ up) (fr-S∙= fr x) = S∙ (free-∋∙' inΔ fr)

free-⊢t' : Δ ⊢t B
         → Free Γ Δ
         → Γ ⊢t B

free-∋∙-∋∙ : Δ ∋∙ X
           → Free Γ Δ
           → Γ ∋∙ X
free-∋∙-∋∙ Z (fr-S∙ fr) = Z
free-∋∙-∋∙ (S∙ inΔ) (fr-S∙ fr) = S∙ (free-∋∙-∋∙ inΔ fr)
free-∋∙-∋∙ (S= inΔ) (fr-S∙= fr x) = S∙ (free-∋∙-∋∙ inΔ fr)
free-∋∙-∋∙ (S⋈ inΔ) fr-⋈ = S⋈ inΔ

free-⊢c-⊢t : Δ ⊢c A
           → Free Γ Δ
           → Γ ⊢t A

free-sregulars' : SRegularS Δ
                → Free Γ Δ
                → SRegularS Γ
free-sregulars' (reg-Z regΓ) fr-⋈ = reg-Z regΓ
free-sregulars' (reg-S∙ regΓ) (fr-S∙ fr) = reg-S∙ (free-sregulars' regΓ fr)
free-sregulars' (reg-S= regΓ regA) (fr-S∙= fr x) = reg-S∙ (free-sregulars' regΓ fr)


data Erasure : Counter m → SCounter → Set where
  era-z : Erasure (Counter m ∋⦂ Z) Z
  era-∞ : Erasure (Counter m ∋⦂ ∞) ∞
  era-𝕚 : Erasure j 𝕟
        → Erasure (𝕚 j) (𝕚 𝕟)
  era-𝕔 : Erasure j 𝕟
        → Erasure (𝕔 j) (𝕔 𝕟)
  era-𝕥 : Erasure j 𝕟
        → Erasure (𝕥₍ A ₎ j) (𝕥 𝕟)

era-↑ty : Erasure j 𝕟
        → j ↑tyʲ k ⇘ j'
        → Erasure j' 𝕟
era-↑ty era-z ↑tyʲ-Z = era-z
era-↑ty era-∞ ↑tyʲ-∞ = era-∞
era-↑ty (era-𝕚 era) (↑tyʲ-𝕚 upj) = era-𝕚 (era-↑ty era upj)
era-↑ty (era-𝕔 era) (↑tyʲ-𝕔 upj) = era-𝕔 (era-↑ty era upj)
era-↑ty (era-𝕥 era) (↑tyʲ-𝕥 upj upA) = era-𝕥 (era-↑ty era upj)

iso-siso : IsoInf j
         → Erasure j 𝕟
         → SIsoInf 𝕟
iso-siso i∞-z (era-𝕚 era-∞) = i∞-z
iso-siso (i∞-i iso) (era-𝕚 era) = i∞-i (iso-siso iso era)

find-sfind : find A k j
           → Erasure j 𝕟
           → Sfind A k 𝕟
find-sfind (f-∞ inA) era-∞ = f-∞ inA
find-sfind (f-iso iso) (era-𝕚 era) = f-iso (iso-siso iso (era-𝕚 era))
find-sfind (f-arr-𝕚-l inA) (era-𝕚 era) = f-arr-𝕚-l inA
find-sfind (f-arr-𝕚-r ¬inA fd) (era-𝕚 era) = f-arr-𝕚-r ¬inA (find-sfind fd era)
find-sfind (f-arr-𝕔 ¬inA fd) (era-𝕔 era) = f-arr-𝕔 ¬inA (find-sfind fd era)
find-sfind (f-∀-𝕚 fd upj) (era-𝕚 era) = f-∀-𝕚 (find-sfind fd (era-𝕚 (era-↑ty era upj)))
find-sfind (f-∀-𝕔 fd upj) (era-𝕔 era) = f-∀-𝕔 (find-sfind fd (era-𝕔 (era-↑ty era upj)))
find-sfind (f-𝕥 fd upj) (era-𝕥 era) = f-𝕥 (find-sfind fd (era-↑ty era upj))

ic-sic : 𝕚𝕔 j
       → Erasure j 𝕟
       → S𝕚𝕔 𝕟
ic-sic case-𝕚 (era-𝕚 era) = case-𝕚
ic-sic case-𝕔 (era-𝕔 era) = case-𝕔



sound : Δ ⊢ j # A ⌞ ≤⁺ ⌝ B ↡ B✦
      → Free Γ Δ
      → Erasure j 𝕟
      → Γ ⊨ 𝕟 # A ≤ B✦

sound- : Δ ⊢ ∞ # A ⌞ ≤⁻ ⌝ B ↡ A✦
      → Free Γ Δ
      → Γ ⊨ ∞ # A✦ ≤ B

sound (s-refl regΔ cloA grd) fr era-z = s-refl (free-sregulars' regΔ fr) (free-⊢c-⊢t cloA fr)
sound (s-int regΔ) fr era-∞ = s-int (free-sregulars' regΔ fr)
sound (s-var-∙ regΔ inΔ) fr era-∞ = s-var-∙ (free-sregulars' regΔ fr) (free-∋∙-∋∙ inΔ fr)
sound (s-arr₁ s s₁) fr era-∞ = s-arr₁ (sound- s fr) (sound s₁ fr era-∞)
sound (s-arr₂ s s₁) fr (era-𝕚 era) = s-arr₂ (sound- s fr) (sound s₁ fr era)
sound (s-arr₃ cloA grd s) fr (era-𝕔 era) = s-arr₃ (free-⊢c-⊢t cloA fr) (sound s fr era)
sound (s-∀ s) fr era-∞ = s-∀ (sound s (fr-S∙ fr) era-∞)
sound (s-∀l s ic fd upj st regB) fr era
  = {!!}
  -- s-∀l (free-⊢t' regB fr) st (sound s fr era) (ic-sic ic era) (find-sfind fd (era-↑ty era upj)) ?
sound (s-∀l-no-appear s ic fd upj st regB) fr era
  = {!!}
  -- s-∀l-no-appear (free-⊢t' regB fr) st (sound s fr era) (ic-sic ic era) fd
sound (s-tapp s upj) fr (era-𝕥 era) = s-tapp (sound s (fr-S∙= fr {!!}) (era-↑ty era upj))
sound (s-svar-l x inΔ) fr era-∞ = s-var-∙ (free-sregulars' x fr) (free-∋∙' inΔ fr)
sound (s-svar-𝕚 x s) fr era = s-var-∙ {!!} (free-∋∙' x fr)
sound (s-svar-𝕔 x s) fr era = s-var-∙ {!!} (free-∋∙' x fr)
sound (s-svar-𝕥 x s) fr era = s-var-∙ {!!} (free-∋∙' x fr)
