module Implicit.SimCounter.Completeness.Main where

open import Implicit.Language.All
open import Implicit.AuxLemmas
open import Implicit.SimCounter.Typing
open import Implicit.SimCounter.Subtyping2
open import Implicit.Interm.All
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

complete (s-refl regΔ cloA grd₁) bd-z fr grd = s-refl (free-sregular regΔ fr) (free-⊢c cloA fr) (free-≫ regΔ grd₁ fr grd)
complete (s-int regΔ) bd-∞ fr grd-int = s-int (free-sregular regΔ fr)
complete (s-var-∙ regΔ inΔ) bd-∞ fr (grd-var= x) = s-svar-l (free-sregular regΔ fr) x
complete (s-var-∙ regΔ inΔ) bd-∞ fr (grd-var∙ x) = s-var-∙ (free-sregular regΔ fr) x
complete (s-arr₁ s s₁) bd-∞ fr (grd-arr grd grd₁) = s-arr₁ (complete- s fr grd) (complete s₁ bd-∞ fr grd₁)
complete (s-arr₂ s s₁) (bd-i bd) fr (grd-arr grd grd₁) = s-arr₂ (complete- s fr grd) (complete s₁ bd fr grd₁)
complete (s-arr₃ cloA grd₁ s) (bd-c bd) fr (grd-arr grd grd₂) = s-arr₃ (free-⊢c cloA fr) (free-≫ (s-sregulars s) grd₁ fr grd) (complete s bd fr grd₂)
complete (s-∀ s) bd-∞ fr (grd-∀ grd) = s-∀ (complete s bd-∞ (fr-S∙ fr) grd)
complete (s-∀l s ic fd upC upD) (bd-c {j = j} {C = E} bd) fr (grd-arr {A% = A%} {B% = B%} grd grd₁)
  with ⟨ j' , upj ⟩ ← ↑tyʲ0-total j
  with ⟨ A%' , upA% ⟩ ← ↑ty0-total A%
  with ⟨ B%' , upB% ⟩ ← ↑ty0-total B%
  with ⟨ E' , upE ⟩ ← ↑ty0-total E
  with reg-S= r regA  ← s-sregulars s
  = s-∀l (complete s (bd-c (bound-weaken=0 bd (⊢t-⊢r regA) upj upD upE)) (fr-S= fr)
                   (≫-weaken= (grd-arr grd grd₁) (▶Z (⊢t-⊢r (free-⊢t regA fr))) (↑ty-arr upC upE) (↑ty-arr upA% upB%)))
                   case-𝕔
                   (sfind-find fd (bd-c (bound-weaken=0 bd ⊢r-int upj upD upE)))
                   upA% upB% (↑tyʲ-𝕔 upj)
complete (s-∀l s ic fd upC upD) (bd-i {j = j} {C = E} bd) fr (grd-arr {A% = A%} {B% = B%} grd grd₁)
  with ⟨ j' , upj ⟩ ← ↑tyʲ0-total j
  with ⟨ A%' , upA% ⟩ ← ↑ty0-total A%
  with ⟨ B%' , upB% ⟩ ← ↑ty0-total B%
  with ⟨ E' , upE ⟩ ← ↑ty0-total E
  with reg-S= r regA  ← s-sregulars s
  = s-∀l (complete s (bd-i (bound-weaken=0 bd (⊢t-⊢r regA) upj upD upE)) (fr-S= fr)
                   (≫-weaken= (grd-arr grd grd₁) (▶Z (⊢t-⊢r (free-⊢t regA fr))) (↑ty-arr upC upE) (↑ty-arr upA% upB%)))
                   case-𝕚
                   (sfind-find fd (bd-i (bound-weaken=0 bd ⊢r-int upj upD upE)))
                   upA% upB% (↑tyʲ-𝕚 upj)
complete (s-tapp s) (bd-t bd upj regT) fr (grd-∀ grd)
  = s-tapp (complete s {!!} (fr-S∙= fr (free-⊢t regT fr)) {!!}) upj
  -- s-tapp (complete s {!!} (fr-S∙= fr (free-⊢t x fr)) {!!}) {!!}
complete (s-svar-l inΓ inΔ) bd-∞ fr grd
  with regA ← ⊢t-⊢r (free-⊢t (∋:=-⊢t inΓ inΔ) fr)
  with refl ← ⊢r-≫-eq' regA grd
  = s-svar-l (free-sregular inΓ fr) (free-∋:=' inΔ fr)
complete (s-svar-𝕚 inΓ s) (bd-i bd) fr (grd-arr grd grd₁) = s-svar-𝕚 (free-∋:=' inΓ fr) (complete s (bd-i bd) fr (grd-arr grd grd₁))
complete (s-svar-𝕔 inΓ s) (bd-c bd) fr (grd-arr grd grd₁) = s-svar-𝕔 (free-∋:=' inΓ fr) (complete s (bd-c bd) fr (grd-arr grd grd₁))
complete (s-svar-𝕥 inΓ s) (bd-t bd upj regT) fr (grd-∀ grd) = s-svar-𝕥 (free-∋:=' inΓ fr) (complete s (bd-t bd upj regT) fr (grd-∀ grd))

complete- (s-int regΔ) fr grd-int = s-int (free-sregular regΔ fr)
complete- (s-var-∙ regΔ inΔ) fr (grd-var= x) = s-svar-r (free-sregular regΔ fr) x
complete- (s-var-∙ regΔ inΔ) fr (grd-var∙ x) = s-var-∙ (free-sregular regΔ fr) x
complete- (s-arr₁ s s₁) fr (grd-arr grd grd₁) = s-arr₁ (complete s bd-∞ fr grd) (complete- s₁ fr grd₁)
complete- (s-∀ s) fr (grd-∀ grd) = s-∀ (complete- s (fr-S∙ fr) grd)
complete- (s-svar-r x inΔ) fr grd
  with regA ← ⊢t-⊢r (free-⊢t (∋:=-⊢t x inΔ) fr)
  with refl ← ⊢r-≫-eq' regA grd = s-svar-r (free-sregular x fr) (free-∋:=' inΔ fr)


complete0 : Γ ⋈ ⊨ 𝕟 # A ⌞ ≤⁺ ⌝ B
          → Bound (Γ ⋈) (⟨ 𝕟 , B ⟩) (⟨ j , C ⟩)
          → Γ ⋈ ⊢ j # A ⌞ ≤⁺ ⌝ C
complete0 ⊢e bd = complete ⊢e bd fr-⋈ (⊢r-≫-eq (bound-⊢r bd (ss-⊢r ⊢e)))

{-
⊢tapp' : Γ ⊢ 𝕥₍ A ₎ j # e ⦂ `∀ B'
        → (up : ↑ty0 B ⇘ B')
        → Γ ⊢ j # e ⓪ A ⦂ B

complete-t : Γ ⊨ 𝕟 # e ⦂ A
           → Bound Γ (⟨ 𝕟 , A ⟩) (⟨ j , B ⟩)
           → Γ ⊢ j # e ⦂ B
complete-t (⊨lit regΓ) bd-z = ⊢lit (tregulars-tregular regΓ)
complete-t (⊨var regΓ x∈Γ) bd-z = ⊢var (tregulars-tregular regΓ) x∈Γ
complete-t (⊨ann ⊢e) bd-z = ⊢ann (complete-t ⊢e bd-∞)
complete-t (⊨lam₁ ⊢e) bd-∞ = ⊢lam₁ (complete-t ⊢e bd-∞)
complete-t (⊨lam₂ ⊢e) (bd-i bd) = ⊢lam₂ (complete-t ⊢e {!!})
complete-t (⊨app₁ ⊢e ⊢e₁) bd = ⊢app₁ (complete-t ⊢e (bd-c bd)) (complete-t ⊢e₁ bd-∞)
complete-t (⊨app₂ ⊢e ⊢e₁) bd = ⊢app₂ (complete-t ⊢e (bd-i bd)) (complete-t ⊢e₁ bd-z)
complete-t (⊨sub ⊢e B≤A gc 𝕟≢Z) bd = ⊢sub (complete-t ⊢e bd-z) (complete0 B≤A {!!}) gc {!!}
complete-t (⊨tabs ⊢e) bd-z = ⊢tabs (complete-t ⊢e bd-z)
complete-t {A = A} {j = j} {B = B} (⊨tapp ⊢e st regA) bd
  with ⟨ A' , upA ⟩ ← ↑ty0-total A
  with ⟨ j' , upj ⟩ ← ↑tyʲ0-total j
  with ⟨ B' , upB ⟩ ← ↑ty0-total B = ⊢tapp' (complete-t ⊢e (bd-t bd regA st upB)) upB
  -}
