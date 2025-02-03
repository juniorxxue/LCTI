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

  ap-closed : Closed Γ
            → Γ ≫ᵍ Γ%
            → Norm Γ%

  ap-closeA : Γ ⊢c A
            → Γ ≫ᵍ Γ%
            → Γ% ≫ A ⇘ A%
            → Γ% ⊢n A%

  ap-∋∙ : Γ ∋∙ X
        → Γ ≫ᵍ Γ%
        → Γ% ∋∙ X

  ap-∋⦂ : Γ ∋ x ⦂ A
        → Γ ≫ᵍ Γ%
        → Γ% ≫ A ⇘ A%
        → Γ% ∋ x ⦂ A%

  ap-weaken,0 : Γ ≫ A ⇘ A%
              → Γ , T ≫ A ⇘ A%

  ap-invar,0 : Γ , T₁ ≫ A ⇘ A%
             → Γ , T₂ ≫ A ⇘ A%

  ape-invar,0 : Γ , T₁ ≫ᵉ e ⇘ e%
              → Γ , T₂ ≫ᵉ e ⇘ e%

  sd-strengthen=0 : Γ ,= T ⊢d j # A' ≤ B'
              → ↑ty0 A ⇘ A'
              → ↑ty0 B ⇘ B'
              → Γ ⊢d j # A ≤ B

  sd-refl-∞ : Norm Γ
            → Γ ⊢d ∞ # A ≤ A

  ap-var=-ap : Γ ∋ X := A
             → Γ ≫ᵍ Γ%
             → Γ% ∋ X := A%
             → Γ% ≫ A ⇘ A%

sound-s : Γ ⊢i j # A ≤ B
        → Γ ≫ᵍ Γ%
        → Γ% ≫ A ⇘ A%
        → Γ% ≫ B ⇘ B%
        → Γ% ⊢d j # A% ≤ B%
sound-s (s-refl cloΓ cloA) apΓ apA apB with ap-unique apA apB
... | refl = s-refl (ap-closed cloΓ apΓ) (ap-closeA cloA apΓ apB)
sound-s (s-int cloΓ) apΓ ap-int ap-int = s-int (ap-closed cloΓ apΓ)
sound-s (s-var-∙ cloΓ inΓ) apΓ apA apB with ap-unique apA apB
... | refl = sd-refl-∞ (ap-closed cloΓ apΓ)
sound-s (s-var-= cloΓ inΓ) apΓ apA apB with ap-unique apA apB
... | refl = sd-refl-∞ (ap-closed cloΓ apΓ)
sound-s (s-arr₁ s s₁) apΓ (ap-arr apA apA₁) (ap-arr apB apB₁) = s-arr₁ (sound-s s apΓ apB apA) (sound-s s₁ apΓ apA₁ apB₁)
sound-s (s-arr₂ s s₁) apΓ (ap-arr apA apA₁) (ap-arr apB apB₁) = s-arr₂ (sound-s s apΓ apB apA) (sound-s s₁ apΓ apA₁ apB₁)
sound-s (s-arr₃ cloA s) apΓ (ap-arr apA apA₁) (ap-arr apB apB₁) with ap-unique apA apB
... | refl = s-arr₃ (ap-closeA cloA apΓ apB) (sound-s s apΓ apA₁ apB₁)
sound-s (s-∀ s) apΓ (ap-∀ apA) (ap-∀ apB) = s-∀ (sound-s s (ap-S∙ apΓ) apA apB)
sound-s (s-∀l s ic fd stC stD) apΓ apA apB = {!!}
sound-s (s-var-l inΓ s) apΓ (ap-var= x) apB = sound-s s apΓ (ap-var=-ap inΓ apΓ x) apB
sound-s (s-var-l inΓ s) apΓ (ap-var∙ x) apB = sound-s s apΓ {!!} apB -- false
sound-s (s-var-r inΓ s) apΓ apA (ap-var= x) = sound-s s apΓ apA (ap-var=-ap inΓ apΓ x)
sound-s (s-var-r inΓ s) apΓ apA (ap-var∙ x) = {!!} -- false

{-
sound-s (s-∀l {B = B} s ic fd upC upD) (ap-∀ {A% = A%} apA) (ap-arr apB apB₁) apΓ =
  let ⟨ A%* , stA% ⟩ = st0-total B A%
  in s-∀l {B = B} stA% (sd-strengthen=0 (sound-s s {!!} {!!} (ap-S= apΓ {!!})) {!!} {!!}) ic {!!}
sound-s (s-var-l inΓ s) (ap-var x) apB apΓ = sound-s s {!!} apB apΓ
sound-s (s-var-r inΓ s) apA (ap-var x) apΓ = sound-s s apA {!!} apΓ
-}

sound : Γ ⊢i j # e ⦂ A
      → Γ ≫ᵍ Γ%
      → Γ% ≫ A ⇘ A%
      → Γ% ≫ᵉ e ⇘ e%
      → Γ% ⊢d j # e% ⦂ A%
sound (⊢lit cloΣ) apΓ ap-int ap-lit = ⊢lit (ap-closed cloΣ apΓ)
sound (⊢var cloΣ x∈Γ) apΓ apA ap-var = ⊢var (ap-closed cloΣ apΓ) (ap-∋⦂ x∈Γ apΓ apA)
sound (⊢ann ⊢e) apΓ apA ape = {!!}
sound (⊢lam₁ ⊢e) apΓ apA ape = {!!}
sound (⊢lam₂ ⊢e) apΓ apA ape = {!!}
sound (⊢app₁ ⊢e ⊢e₁) apΓ apA ape = {!!}
sound (⊢app₂ ⊢e ⊢e₁) apΓ apA ape = {!!}
sound (⊢sub ⊢e B≤A j≢Z) apΓ apA ape = {!!}
sound (⊢tabs ⊢e) apΓ apA ape = {!!}

{-
sound (⊢var cloΣ x∈Γ) apA ap-var apΓ = ⊢var (ap-closed cloΣ apΓ) (ap-∋⦂ x∈Γ apΓ apA)
sound (⊢ann ⊢e) apA (ap-ann x ape) apΓ with ap-unique apA x
... | refl = ⊢ann (sound ⊢e apA ape apΓ)
sound (⊢lam₁ ⊢e) (ap-arr apA apA₁) (ap-lam ape) apΓ =
  ⊢lam₁ (sound ⊢e (ap-weaken,0 apA₁) (ape-invar,0 ape) (ap-S, apΓ apA))
sound (⊢lam₂ ⊢e) (ap-arr apA apA₁) (ap-lam ape) apΓ =
  ⊢lam₂ (sound ⊢e (ap-weaken,0 apA₁) (ape-invar,0 ape) (ap-S, apΓ apA))
sound (⊢app₁ ⊢e ⊢e₁) apA (ap-app ape ape₁) apΓ = {!!}
-- with ap-total (t-cloA ⊢e₁)
-- ... | ⟨ A%' , ap' ⟩ = ⊢app₁ (sound ⊢e (ap-arr ap' apA) ape apΓ) (sound ⊢e₁ ap' ape₁ apΓ)
sound (⊢app₂ ⊢e ⊢e₁) apA (ap-app ape ape₁) apΓ with ap-total (t-cloA ⊢e₁)
... | ⟨ A%' , ap' ⟩ = ⊢app₂ (sound ⊢e (ap-arr ap' apA) ape apΓ) (sound ⊢e₁ ap' ape₁ apΓ)
sound (⊢sub ⊢e B≤A j≢Z) apA ape apΓ with ap-total (t-cloA ⊢e)
... | ⟨ A% , ap ⟩ = ⊢sub (sound ⊢e ap ape apΓ) (sound-s B≤A ap apA apΓ) j≢Z
sound (⊢tabs ⊢e) (ap-∀ apA) (ap-tlam ape) apΓ = ⊢tabs (sound ⊢e apA ape (ap-S∙ apΓ))
-}
