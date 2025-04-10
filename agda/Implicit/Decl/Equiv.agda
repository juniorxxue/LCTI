module Implicit.Decl.Equiv where

open import Implicit.Language.All
open import Implicit.Decl.Subtyping renaming (_⊢_#_⌞_⌝_ to _⊢¹_#_⌞_⌝_)
open import Implicit.Decl.SubtypingV2 renaming (_⊢_#_⌞_⌝_ to _⊢²_#_⌞_⌝_)


sound : Γ ⊢¹ j # A ⌞ ≤ ⌝ B
      → Γ ⊢² j # A ⌞ ≤ ⌝ B
sound (s-refl regΔ cloA) = s-refl regΔ cloA
sound (s-int regΔ) = s-int regΔ
sound (s-var-∙ regΔ inΔ) = s-var-∙ regΔ inΔ
sound (s-arr₁ s s₁) = s-arr₁ (sound s) (sound s₁)
sound (s-arr₂ s s₁) = s-arr₂ (sound s) (sound s₁)
sound (s-arr₃ s) = s-arr₃ (sound s)
sound (s-∀ s) = s-∀ (sound s)
sound (s-∀l {B = B} {C = C} {D = D} st s ic fd upj)
  with ⟨ C' , upC ⟩ ← ↑ty0-total C
  with ⟨ D' , upD ⟩ ← ↑ty0-total D = s-∀l {B = B} {!!} {!sound s!} ic fd upC upD upj
sound (s-tapp st s upC) = s-tapp {!!} {!!} {!!}


complete : Γ ⊢² j # A ⌞ ≤ ⌝ B
         → Γ ⊢¹ j # A ⌞ ≤ ⌝ B
complete (s-refl regΔ cloA) = s-refl regΔ cloA
complete (s-int regΔ) = s-int regΔ
complete (s-var-∙ regΔ inΔ) = s-var-∙ regΔ inΔ
complete (s-arr₁ s s₁) = s-arr₁ (complete s) (complete s₁)
complete (s-arr₂ s s₁) = s-arr₂ (complete s) (complete s₁)
complete (s-arr₃ s) = s-arr₃ (complete s)
complete (s-∀ s) = s-∀ (complete s)
complete (s-∀l grd s ic fd upC upD upj) = s-∀l {!!} {!!} ic fd upj
complete (s-tapp x s upC) = s-tapp {!!} {!!} {!!}
