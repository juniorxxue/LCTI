module Implicit.SoundInterm where

open import Implicit.Language hiding (_≤_)
open import Implicit.Decl renaming (_⊢_#_⦂_ to _⊢d_#_⦂_; _⊢_#_≤_ to _⊢d_#_≤_)
open import Implicit.Interm renaming (_⊢_#_⦂_ to _⊢i_#_⦂_; _⊢_#_≤_ to _⊢i_#_≤_)

postulate
  ap-total : Γ ⊢c A
           → ∃[ A% ](Γ ≫ A ⇘ A%)

  ap-unique : Γ ≫ A ⇘ A%
            → Γ ≫ A ⇘ B%
            → A% ≡ B%

  apx-unique : Γ ≫ˣ X ⇘ A%
             → Γ ≫ˣ X ⇘ B%
             → A% ≡ B%

  ap-closed : Closed Γ
            → Γ ≫ᵍ Γ%
            → Norm Γ%

  ap-closeA : Γ ⊢c A
            → Γ ≫ᵍ Γ%
            → Γ ≫ A ⇘ A%
            → Γ% ⊢n A%

  ap-∋∙ : Γ ∋∙ X
        → Γ ≫ᵍ Γ%
        → Γ% ∋∙ X

  ap-∋⦂ : Γ ∋ x ⦂ A
        → Γ ≫ᵍ Γ%
        → Γ ≫ A ⇘ A%
        → Γ% ∋ x ⦂ A%

  ap-weaken,0 : Γ ≫ A ⇘ A%
              → Γ , T ≫ A ⇘ A%

  ap-invar,0 : Γ , T₁ ≫ A ⇘ A%
             → Γ , T₂ ≫ A ⇘ A%

  ape-invar,0 : Γ , T₁ ≫ᵉ e ⇘ e%
              → Γ , T₂ ≫ᵉ e ⇘ e%

  apx-uvar : Γ ≫ˣ X ⇘ A%
           → Γ ∋∙ X
           → A% ≡ ‶ X

  ap-var= : Γ ∋ X := A
          → Γ ≫ˣ X ⇘ A%
          → Γ ≫ A ⇘ A%

  sd-strengthen=0 : Γ ,= T ⊢d j # A' ≤ B'
              → ↑ty0 A ⇘ A'
              → ↑ty0 B ⇘ B'
              → Γ ⊢d j # A ≤ B

  sd-refl-∞ : Norm Γ
            → Γ ⊢d ∞ # A ≤ A

sound-s : Γ ⊢i j # A ≤ B
        → Γ ≫ A ⇘ A%
        → Γ ≫ B ⇘ B%
        → Γ ≫ᵍ Γ%
        → Γ% ⊢d j # A% ≤ B%
sound-s (s-refl cloΓ cloA) apA apB apΓ with ap-unique apA apB
... | refl = s-refl (ap-closed cloΓ apΓ) (ap-closeA cloA apΓ apB)
sound-s (s-int cloΓ) ap-int ap-int apΓ = s-int (ap-closed cloΓ apΓ)
sound-s (s-var-∙ cloΓ inΓ) (ap-var x) (ap-var x₁) apΓ with apx-uvar x inΓ | apx-uvar x₁ inΓ
... | refl | refl = s-var-∙ (ap-closed cloΓ apΓ) (ap-∋∙ inΓ apΓ)
sound-s (s-var-= cloΓ inΓ) (ap-var x) (ap-var x₁) apΓ with apx-unique x x₁
... | refl = sd-refl-∞ (ap-closed cloΓ apΓ)
sound-s (s-arr₁ s s₁) (ap-arr apA apA₁) (ap-arr apB apB₁) apΓ = s-arr₁ (sound-s s apB apA apΓ) (sound-s s₁ apA₁ apB₁ apΓ)
sound-s (s-arr₂ s s₁) (ap-arr apA apA₁) (ap-arr apB apB₁) apΓ = s-arr₂ (sound-s s apB apA apΓ) (sound-s s₁ apA₁ apB₁ apΓ)
sound-s (s-arr₃ cloA s) (ap-arr apA apA₁) (ap-arr apB apB₁) apΓ with ap-unique apA apB
... | refl = s-arr₃ (ap-closeA cloA apΓ apB) (sound-s s apA₁ apB₁ apΓ)
sound-s (s-∀ s) (ap-∀ apA) (ap-∀ apB) apΓ = s-∀ (sound-s s apA apB (ap-S∙ apΓ))
sound-s (s-∀l {B = B} s ic fd upC upD) (ap-∀ apA) (ap-arr apB apB₁) apΓ =
  s-∀l {B = B} {!!} {!!} {!!} {!!}
sound-s (s-var-l inΓ s) (ap-var x) apB apΓ = sound-s s (ap-var= inΓ x) apB apΓ
sound-s (s-var-r inΓ s) apA (ap-var x) apΓ = sound-s s apA (ap-var= inΓ x) apΓ

sound : Γ ⊢i j # e ⦂ A
      → Γ ≫ A ⇘ A%
      → Γ ≫ᵉ e ⇘ e%
      → Γ ≫ᵍ Γ%
      → Γ% ⊢d j # e% ⦂ A%
sound (⊢lit cloΣ) ap-int ap-lit apΓ = ⊢lit (ap-closed cloΣ apΓ)
sound (⊢var cloΣ x∈Γ) apA ap-var apΓ = ⊢var (ap-closed cloΣ apΓ) (ap-∋⦂ x∈Γ apΓ apA)
sound (⊢ann ⊢e) apA (ap-ann x ape) apΓ with ap-unique apA x
... | refl = ⊢ann (sound ⊢e apA ape apΓ)
sound (⊢lam₁ ⊢e) (ap-arr apA apA₁) (ap-lam ape) apΓ =
  ⊢lam₁ (sound ⊢e (ap-weaken,0 apA₁) (ape-invar,0 ape) (ap-S, apΓ apA))
sound (⊢lam₂ ⊢e) (ap-arr apA apA₁) (ap-lam ape) apΓ =
  ⊢lam₂ (sound ⊢e (ap-weaken,0 apA₁) (ape-invar,0 ape) (ap-S, apΓ apA))
sound (⊢app₁ ⊢e ⊢e₁) apA (ap-app ape ape₁) apΓ with ap-total (t-cloA ⊢e₁)
... | ⟨ A%' , ap' ⟩ = ⊢app₁ (sound ⊢e (ap-arr ap' apA) ape apΓ) (sound ⊢e₁ ap' ape₁ apΓ)
sound (⊢app₂ ⊢e ⊢e₁) apA (ap-app ape ape₁) apΓ with ap-total (t-cloA ⊢e₁)
... | ⟨ A%' , ap' ⟩ = ⊢app₂ (sound ⊢e (ap-arr ap' apA) ape apΓ) (sound ⊢e₁ ap' ape₁ apΓ)
sound (⊢sub ⊢e B≤A j≢Z) apA ape apΓ with ap-total (t-cloA ⊢e)
... | ⟨ A% , ap ⟩ = ⊢sub (sound ⊢e ap ape apΓ) (sound-s B≤A ap apA apΓ) j≢Z
sound (⊢tabs ⊢e) (ap-∀ apA) (ap-tlam ape) apΓ = ⊢tabs (sound ⊢e apA ape (ap-S∙ apΓ))
