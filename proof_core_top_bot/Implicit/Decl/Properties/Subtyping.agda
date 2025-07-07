module Implicit.Decl.Properties.Subtyping where

open import Implicit.Language.All
open import Implicit.AuxLemmas
open import Implicit.Decl.Subtyping


s-block-l : Δ ⊢ j # A ≤ B
          → Δ ⊢⊠ A
          → Δ ⊢⊠ B

s-block-r : Δ ⊢ j # A ≤ B
          → Δ ⊢⊠ B
          → Δ ⊢⊠ A

s-block-l (s-refl regΔ cloA) bloA = {!!}
s-block-l (s-int regΔ) bloA = {!!}
s-block-l (s-var-∙ regΔ inΔ) bloA = {!!}
s-block-l (s-arr₁ s s₁) bloA = {!!}
s-block-l (s-arr₂ s s₁) bloA = {!!}
s-block-l (s-arr₃ regA s) bloA = {!!}
s-block-l (s-∀ s) bloA = {!!}
s-block-l (s-∀l regB st s ic fd upj) bloA = {!s-block-r s!}
s-block-l (s-∀l-no-appear regB st s ic fd) bloA = {!!}
s-block-l (s-tapp regB st s upC) bloA = {!!}

s-block-r (s-refl regΔ cloA) bloB = {!!}
s-block-r (s-int regΔ) bloB = {!!}
s-block-r (s-var-∙ regΔ inΔ) bloB = {!!}
s-block-r (s-arr₁ s s₁) bloB = {!!}
s-block-r (s-arr₂ s s₁) bloB = {!!}
s-block-r (s-arr₃ regA s) bloB = {!!}
s-block-r (s-∀ s) bloB = {!!}
s-block-r (s-∀l regB st s ic fd upj) bloB = {!!}
s-block-r (s-∀l-no-appear regB st s ic fd) bloB = {!!}
s-block-r (s-tapp regB st s upC) bloB = {!!}

{-
s-¬ε-l : Δ ⊢ j # A ≤ B
        → k ¬ε A
        → k ¬ε B

s-¬ε-r : Δ ⊢ j # A ≤ B
        → k ¬ε B
        → k ¬ε A

s-¬ε-l (s-refl regΔ cloA) ninA = ninA
s-¬ε-l (s-int regΔ) ninA = ninA
s-¬ε-l (s-var-∙ regΔ inΔ) ninA = ninA
s-¬ε-l (s-arr₁ s s₁) (¬ε-arr ninA ninA₁) = ¬ε-arr (s-¬ε-r s ninA) (s-¬ε-l s₁ ninA₁)
s-¬ε-l (s-arr₂ s s₁) (¬ε-arr ninA ninA₁) = ¬ε-arr (s-¬ε-r s ninA) (s-¬ε-l s₁ ninA₁)
s-¬ε-l (s-arr₃ regA s) (¬ε-arr ninA ninA₁) = ¬ε-arr ninA (s-¬ε-l s ninA₁)
s-¬ε-l (s-∀ s) (¬ε-∀ ninA) = ¬ε-∀ (s-¬ε-l s ninA)
s-¬ε-l (s-∀l regB st s ic fd upj) (¬ε-∀ ninA) = s-¬ε-l s {!ninA!}
s-¬ε-l (s-∀l-no-appear regB st s ic fd) (¬ε-∀ ninA) = s-¬ε-l s {!!}
s-¬ε-l (s-tapp regB st s upC) (¬ε-∀ ninA) = ¬ε-∀ {!s-¬ε-l s ?!}

s-¬ε-r (s-refl regΔ cloA) ninB = ninB
s-¬ε-r (s-int regΔ) ninB = ninB
s-¬ε-r (s-var-∙ regΔ inΔ) ninB = ninB
s-¬ε-r (s-arr₁ s s₁) (¬ε-arr ninB ninB₁) = ¬ε-arr (s-¬ε-l s ninB) (s-¬ε-r s₁ ninB₁)
s-¬ε-r (s-arr₂ s s₁) (¬ε-arr ninB ninB₁) = ¬ε-arr (s-¬ε-l s ninB) (s-¬ε-r s₁ ninB₁)
s-¬ε-r (s-arr₃ regA s) (¬ε-arr ninB ninB₁) = ¬ε-arr ninB (s-¬ε-r s ninB₁)
s-¬ε-r (s-∀ s) (¬ε-∀ ninB) = ¬ε-∀ (s-¬ε-r s ninB)
s-¬ε-r (s-∀l regB st s ic fd upj) ¬ε'@(¬ε-arr ninB ninB₁)
  with ih ← s-¬ε-r s ¬ε' = {!ih!}
s-¬ε-r (s-∀l-no-appear regB st s ic fd) ninB
  with ih ← s-¬ε-r s ninB = {!ih!}
s-¬ε-r (s-tapp regB st s upC) (¬ε-∀ ninB)
  with ih ← s-¬ε-r s (¬ε-↑ty-≤ ninB upC z≤n) = {!ih!}
-}
