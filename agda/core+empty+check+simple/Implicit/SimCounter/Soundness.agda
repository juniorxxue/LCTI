module Implicit.SimCounter.Soundness where

open import Implicit.Language.All
open import Implicit.Decl.Typing
open import Implicit.Decl.Subtyping
open import Implicit.SimCounter.Typing
open import Implicit.SimCounter.Subtyping


infix 3 _R_
data _R_ : Counter m × Type m → SCounter × Type m → Set where
  R-Z : ⟨ Z , A ⟩ R ⟨ Z , A ⟩
  R-∞ : ⟨ ∞ , A ⟩ R ⟨ ∞ , A ⟩
  R-𝕚 : ⟨ j , B ⟩ R ⟨ 𝕟 , C ⟩
      → ⟨ 𝕚 j , A `→ B ⟩ R ⟨ 𝕚 𝕟 , A `→ C ⟩
  R-𝕔 : ⟨ j , B ⟩ R ⟨ 𝕟 , C ⟩
      → ⟨ 𝕔 j , A `→ B ⟩ R ⟨ 𝕔 𝕟 , A `→ C ⟩
  R-𝕥 : ⟨ j , A* ⟩ R ⟨ 𝕟 , B* ⟩
      → ⟦ T ⟧ B ⇘ B*
      → ⟦ T ⟧ A ⇘ A*
      → ⟨ 𝕥₍ T ₎ j , `∀ A ⟩ R ⟨ 𝕥 𝕟 , `∀ B ⟩

exist-st-r : ⟨ j , A ⟩ R ⟨ 𝕟 , B ⟩
           → ⟦ T ⟧ C ⇘ A
           → ∃[ D ](⟦ T ⟧ D ⇘ B)
exist-st-r {C = C} R-Z st = ⟨ C , st ⟩
exist-st-r {C = C} R-∞ st = ⟨ C , st ⟩
exist-st-r (R-𝕚 rr) (st-var stx) = {!!}
exist-st-r (R-𝕚 rr) (st-arr st st₁) = {!!}
exist-st-r (R-𝕔 rr) st = {!!}
exist-st-r (R-𝕥 rr x x₁) st = {!!}

old→new-s : Γ ⊢ j # A ≤ B
          → ⟨ j , B ⟩ R ⟨ 𝕟 , C ⟩
          → Γ ⊨ 𝕟 # A ≤ C
old→new-s (s-refl regΔ cloA) R-Z = s-refl regΔ cloA
old→new-s (s-int regΔ) R-∞ = s-int regΔ
old→new-s (s-var-∙ regΔ inΔ) R-∞ = s-var-∙ regΔ inΔ
old→new-s (s-arr₁ s s₁) R-∞ = s-arr₁ (old→new-s s R-∞) (old→new-s s₁ R-∞)
old→new-s (s-arr₂ s s₁) (R-𝕚 rr) = s-arr₂ (old→new-s s R-∞) (old→new-s s₁ rr)
old→new-s (s-arr₃ regA s) (R-𝕔 rr) = s-arr₃ regA (old→new-s s rr)
old→new-s (s-∀ s) R-∞ = s-∀ (old→new-s s R-∞)
old→new-s (s-∀l regB st s ic fd upj) rr = {!!}
old→new-s (s-∀l-no-appear regB st s ic fd) rr = {!!}
old→new-s (s-tapp regB st s upC) (R-𝕥 rr x x₁)
  with refl ← ↑ty-st-eq upC x₁ = s-tapp {!!}

old→new : Γ ⊢ j # e ⦂ A
        → ⟨ j , A ⟩ R ⟨ 𝕟 , B ⟩
        → Γ ⊨ 𝕟 # e ⦂ B
old→new (⊢lit regΓ) R-Z = ⊨lit regΓ
old→new (⊢var regΓ x∈Γ) R-Z = ⊨var regΓ x∈Γ
old→new (⊢ann ⊢e) R-Z = ⊨ann (old→new ⊢e R-∞)
old→new (⊢lam₁ ⊢e) R-∞ = ⊨lam₁ (old→new ⊢e R-∞)
old→new (⊢lam₂ ⊢e) (R-𝕚 rr) = ⊨lam₂ (old→new ⊢e rr)
old→new (⊢app₁ ⊢e ⊢e₁) rr = ⊨app₁ (old→new ⊢e (R-𝕔 rr)) (old→new ⊢e₁ R-∞)
old→new (⊢app₂ ⊢e ⊢e₁) rr = ⊨app₂ (old→new ⊢e (R-𝕚 rr)) (old→new ⊢e₁ R-Z)
old→new (⊢sub ⊢e B≤A gc j≢Z) rr = ⊨sub (old→new ⊢e R-Z) (old→new-s B≤A rr) gc {!!}
old→new (⊢tabs ⊢e) R-Z = ⊨tabs (old→new ⊢e R-Z)
old→new (⊢tapp ⊢e st) rr
  with ⟨ pre , st' ⟩ ← exist-st-r rr st = ⊨tapp (old→new ⊢e (R-𝕥 rr st' st)) st'
