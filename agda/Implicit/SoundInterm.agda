module Implicit.SoundInterm where

open import Implicit.Language hiding (_≤_)
open import Implicit.Decl renaming (_⊢_#_⦂_ to _⊢d_#_⦂_; _⊢_#_≤_ to _⊢d_#_≤_)
open import Implicit.Interm renaming (_⊢_#_⦂_ to _⊢i_#_⦂_; _⊢_#_≤_ to _⊢i_#_≤_)
open import Implicit.SoundIntermAux

postulate

  ap-∋⦂ : Γ ∋ x ⦂ A
        → Γ ≫ᵍ Γ%
        → Γ% ≫ A ⇘ A%
        → Γ% ∋ x ⦂ A%

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

sound-s : Γ ⊢i j # A ≤ B
        → Γ ≫ᵍ Γ%
        → Γ% ≫ A ⇘ A%
        → Γ% ≫ B ⇘ B%
        → Γ% ⊢d j # A% ≤ B%
sound-s (s-refl cloΓ cloA) apΓ apA apB with ap-unique apA apB
... | refl = s-refl (ap-closed cloΓ apΓ) (ap-closeA cloA apΓ (ap-closed cloΓ apΓ) apB)
sound-s (s-int cloΓ) apΓ ap-int ap-int = s-int (ap-closed cloΓ apΓ)
sound-s (s-var-∙ cloΓ inΓ) apΓ apA apB with ap-unique apA apB
... | refl = sd-refl-∞ (ap-closed cloΓ apΓ)
sound-s (s-var-= cloΓ inΓ) apΓ apA apB with ap-unique apA apB
... | refl = sd-refl-∞ (ap-closed cloΓ apΓ)
sound-s (s-arr₁ s s₁) apΓ (ap-arr apA apA₁) (ap-arr apB apB₁) = s-arr₁ (sound-s s apΓ apB apA) (sound-s s₁ apΓ apA₁ apB₁)
sound-s (s-arr₂ s s₁) apΓ (ap-arr apA apA₁) (ap-arr apB apB₁) = s-arr₂ (sound-s s apΓ apB apA) (sound-s s₁ apΓ apA₁ apB₁)
sound-s (s-arr₃ cloA s) apΓ (ap-arr apA apA₁) (ap-arr apB apB₁) with ap-unique apA apB
... | refl = s-arr₃ (ap-closeA cloA apΓ (ap-closed (s-cloΓ s) apΓ) apB) (sound-s s apΓ apA₁ apB₁)
sound-s (s-∀ s) apΓ (ap-∀ apA) (ap-∀ apB) = s-∀ (sound-s s (ap-S∙ apΓ) apA apB)
sound-s (s-∀l s ic fd stC stD) apΓ apA apB = {!!}
sound-s (s-var-l inΓ s) apΓ (ap-var= x) apB = sound-s s apΓ (ap-var=-ap inΓ apΓ x) apB
sound-s (s-var-l inΓ s) apΓ (ap-var∙ x) apB = ⊥-elim (∙∈-:=∈-false (ap-∋∙-rev x apΓ) inΓ)
sound-s (s-var-r inΓ s) apΓ apA (ap-var= x) = sound-s s apΓ apA (ap-var=-ap inΓ apΓ x)
sound-s (s-var-r inΓ s) apΓ apA (ap-var∙ x) = ⊥-elim (∙∈-:=∈-false (ap-∋∙-rev x apΓ) inΓ)

{-
sound-s (s-∀l {B = B} s ic fd upC upD) (ap-∀ {A% = A%} apA) (ap-arr apB apB₁) apΓ =
  let ⟨ A%* , stA% ⟩ = st0-total B A%
  in s-∀l {B = B} stA% (sd-strengthen=0 (sound-s s {!!} {!!} (ap-S= apΓ {!!})) {!!} {!!}) ic {!!}
-}

sound : Γ ⊢i j # e ⦂ A
      → Γ ≫ᵍ Γ%
      → Γ% ≫ A ⇘ A%
      → Γ% ≫ᵉ e ⇘ e%
      → Γ% ⊢d j # e% ⦂ A%
sound (⊢lit cloΣ) apΓ ap-int ap-lit = ⊢lit (ap-closed cloΣ apΓ)
sound (⊢var cloΣ x∈Γ) apΓ apA ap-var = ⊢var (ap-closed cloΣ apΓ) (ap-∋⦂ x∈Γ apΓ apA)
sound (⊢ann ⊢e) apΓ apA (ap-ann apA₁ ape) with ap-unique apA apA₁
... | refl = ⊢ann (sound ⊢e apΓ apA ape)
sound (⊢lam₁ ⊢e) apΓ (ap-arr apA apA₁) (ap-lam ape) =
  ⊢lam₁ (sound ⊢e (ap-S, apΓ apA) (ap-weaken,0 apA₁) (ape-invar,0 ape))
sound (⊢lam₂ ⊢e) apΓ (ap-arr apA apA₁) (ap-lam ape) =
  ⊢lam₂ (sound ⊢e (ap-S, apΓ apA) (ap-weaken,0 apA₁) (ape-invar,0 ape))
sound {Γ% = Γ%} (⊢app₁ ⊢e ⊢e₁) apΓ apA (ap-app ape ape₁) with ap-total {Γ = Γ%} {!!}
... | ⟨ A%' , ap' ⟩ = ⊢app₁ (sound ⊢e apΓ (ap-arr ap' apA) ape) (sound ⊢e₁ apΓ ap' ape₁)
sound (⊢app₂ ⊢e ⊢e₁) apΓ apA ape = {!!}
sound (⊢sub ⊢e B≤A j≢Z) apΓ apA ape = {!!}
sound (⊢tabs ⊢e) apΓ (ap-∀ apA) (ap-tlam ape) = ⊢tabs (sound ⊢e (ap-S∙ apΓ) apA ape)

{-
sound (⊢app₁ ⊢e ⊢e₁) apA (ap-app ape ape₁) apΓ = {!!}
-- with ap-total (t-cloA ⊢e₁)
-- ... | ⟨ A%' , ap' ⟩ = ⊢app₁ (sound ⊢e (ap-arr ap' apA) ape apΓ) (sound ⊢e₁ ap' ape₁ apΓ)
sound (⊢app₂ ⊢e ⊢e₁) apA (ap-app ape ape₁) apΓ with ap-total (t-cloA ⊢e₁)
... | ⟨ A%' , ap' ⟩ = ⊢app₂ (sound ⊢e (ap-arr ap' apA) ape apΓ) (sound ⊢e₁ ap' ape₁ apΓ)
sound (⊢sub ⊢e B≤A j≢Z) apA ape apΓ with ap-total (t-cloA ⊢e)
... | ⟨ A% , ap ⟩ = ⊢sub (sound ⊢e ap ape apΓ) (sound-s B≤A ap apA apΓ) j≢Z
sound (⊢tabs ⊢e) (ap-∀ apA) (ap-tlam ape) apΓ = ⊢tabs (sound ⊢e apA ape (ap-S∙ apΓ))
-}
