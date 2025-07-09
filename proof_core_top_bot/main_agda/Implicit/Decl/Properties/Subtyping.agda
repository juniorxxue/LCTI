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
