module Implicit.Decl.Properties.Trans where

open import Implicit.Language.All
open import Implicit.Decl.Subtyping


s-refl' : SRegular Γ
       → Γ ⊢r A
       → Γ ⊢ ∞ # A ≤ A
s-refl' regΓ ⊢r-int = s-int regΓ
s-refl' regΓ ⊢r-top = s-top regΓ ⊢r-top
s-refl' regΓ ⊢r-bot = s-bot regΓ ⊢r-bot rj-∞
s-refl' regΓ (⊢r-var-∙ inΓ) = s-var-∙ regΓ inΓ
s-refl' regΓ (⊢r-arr regA regA₁) = s-arr₁ (s-refl' regΓ regA) (s-refl' regΓ regA₁)
s-refl' regΓ (⊢r-∀ regA) = s-∀ (s-refl' (reg-S∙ regΓ) regA)


s-trans' : Γ ⊢ j # A ≤ B
        → Γ ⊢ j # B ≤ C
        → Γ ⊢ j # A ≤ C
s-trans' (s-refl regΔ cloA) (s-refl regΔ₁ cloA₁) = s-refl regΔ cloA₁
s-trans' (s-int regΔ) (s-int regΔ₁) = s-int regΔ
s-trans' (s-var-∙ regΔ inΔ) (s-var-∙ regΔ₁ inΔ₁) = s-var-∙ regΔ inΔ₁
s-trans' (s-arr₁ s1 s3) (s-arr₁ s2 s4) = s-arr₁ (s-trans' s2 s1) (s-trans' s3 s4)
s-trans' (s-arr₂ s1 s3) (s-arr₂ s2 s4) = s-arr₂ (s-trans' s2 s1) (s-trans' s3 s4)
s-trans' (s-arr₃ regA s1) (s-arr₃ regA₁ s2) = s-arr₃ regA (s-trans' s1 s2)
s-trans' (s-∀ s1) (s-∀ s2) = s-∀ (s-trans' s1 s2)
s-trans' (s-∀l regB st s1 ic fd upj) (s-arr₂ s2 s3) = s-∀l regB st (s-trans' s1 (s-arr₂ s2 s3)) ic fd upj
s-trans' (s-∀l regB st s1 ic fd upj) (s-arr₃ regA s2) = s-∀l regB st (s-trans' s1 (s-arr₃ regA s2)) ic fd upj
s-trans' (s-∀l-no-appear regB st s1 ic fd) (s-arr₂ s2 s3) = s-∀l-no-appear regB st (s-trans' s1 (s-arr₂ s2 s3)) ic fd
s-trans' (s-∀l-no-appear regB st s1 ic fd) (s-arr₃ regA s2) = s-∀l-no-appear regB st (s-trans' s1 (s-arr₃ regA s2)) ic fd
s-trans' (s-tapp regB st s1 upC) (s-tapp regB₁ st₁ s2 upC₁)
  with refl ← ↑ty-st-eq upC st₁ = s-tapp regB st (s-trans' s1 s2) upC₁
s-trans' (s-bot regΔ regA regj) s = s-bot regΔ (s1-⊢r-r s) regj
s-trans' (s-top regΔ regA) (s-top regΔ₁ regA₁) = s-top regΔ regA
s-trans' (s-refl regΔ cloA) (s-bot regΔ₁ regA regj) = s-bot regΔ regA regj
s-trans' (s-int regΔ) (s-top regΔ₁ regA) = s-top regΔ regA
s-trans' {C = Top} (s-var-∙ regΔ inΔ) x = x
s-trans' {C = Top} (s-arr₁ x₁ x₂) x = s-top (s1-sregular x₁) (⊢r-arr (s1-⊢r-r x₁) (s1-⊢r-l x₂))
s-trans' {C = Top} (s-∀ x₁) x = s-top (s1-sregular x) (⊢r-∀ (s1-⊢r-l x₁))
s-trans' {C = C `→ C₁} (s-∀ x₁) (s-∀l regB st x () fd upj)
s-trans' {C = C `→ C₁} (s-∀ x₁) (s-∀l-no-appear regB st x () fd)
