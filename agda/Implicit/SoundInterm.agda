module Implicit.SoundInterm where

open import Implicit.Language hiding (_≤_)
open import Implicit.Decl renaming (_⊢_#_⦂_ to _⊢d_#_⦂_; _⊢_#_≤_ to _⊢d_#_≤_)
open import Implicit.Interm renaming (_⊢_#_⦂_ to _⊢i_#_⦂_; _⊢_#_≤_ to _⊢i_#_≤_)
open import Implicit.SoundIntermAux
open import Implicit.SoundIntermAux2

postulate

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

ap-ε : k ε A
     → Γ ∋∙ k
     → Γ ≫ A ⇘ A%
     → k ε A%
ap-ε ε-var inΓ (ap-var= x) = ⊥-elim (∙∈-:=∈-false inΓ x)
ap-ε ε-var inΓ (ap-var∙ x) = ε-var
ap-ε (ε-arr-l inA) inΓ (ap-arr apA apA₁) = ε-arr-l (ap-ε inA inΓ apA)
ap-ε (ε-arr-r inA) inΓ (ap-arr apA apA₁) = ε-arr-r (ap-ε inA inΓ apA₁)
ap-ε (ε-∀ inA) inΓ (ap-∀ apA) = ε-∀ (ap-ε inA (S∙ inΓ) apA)

ap-ε-rev : k ε A%
         → k ¬εᵍ Γ
         → Γ ∋∙ k
         → Γ ≫ A ⇘ A%
         → k ε A
ap-ε-rev ε-var ninΓ inΓ (ap-var= x) = ⊥-elim (εᵍ-false x ε-var ninΓ)
ap-ε-rev ε-var ninΓ inΓ (ap-var∙ x) = ε-var
ap-ε-rev (ε-arr-l inA%) ninΓ inΓ (ap-var= x) = ⊥-elim (εᵍ-false x (ε-arr-l inA%) ninΓ)
ap-ε-rev (ε-arr-l inA%) ninΓ inΓ (ap-arr apA apA₁) = ε-arr-l (ap-ε-rev inA% ninΓ inΓ apA)
ap-ε-rev (ε-arr-r inA%) ninΓ inΓ (ap-var= x) = ⊥-elim (εᵍ-false x (ε-arr-r inA%) ninΓ)
ap-ε-rev (ε-arr-r inA%) ninΓ inΓ (ap-arr apA apA₁) = ε-arr-r (ap-ε-rev inA% ninΓ inΓ apA₁)
ap-ε-rev (ε-∀ inA%) ninΓ inΓ (ap-var= x) = ⊥-elim (εᵍ-false x (ε-∀ inA%) ninΓ)
ap-ε-rev (ε-∀ inA%) ninΓ inΓ (ap-∀ apA) = ε-∀ (ap-ε-rev inA% (S∙ ninΓ) (S∙ inΓ) apA)

ap-¬ε : ¬ (k ε A)
      → k ¬εᵍ Γ
      → Γ ∋∙ k
      → Γ ≫ A ⇘ A%
      → k ε A%
      → ⊥
ap-¬ε ninA ninΓ inΓ apA inA% = ninA (ap-ε-rev inA% ninΓ inΓ apA)

ap-find' : find A k j
         → Γ ∋∙ k
         → k ¬εᵍ Γ
         → Γ ≫ A ⇘ A%
         → find A% k j
ap-find' (f-∞ x) inΓ ninΓ apA = f-∞ (ap-ε x inΓ apA)
ap-find' (f-arr-𝕚-l x) inΓ ninΓ (ap-arr apA apA₁) = f-arr-𝕚-l (ap-ε x inΓ apA)
ap-find' (f-arr-𝕚-r fd) inΓ ninΓ (ap-arr apA apA₁) = f-arr-𝕚-r (ap-find' fd inΓ ninΓ apA₁)
ap-find' (f-arr-𝕔 ¬inA fd) inΓ ninΓ (ap-arr apA apA₁) = f-arr-𝕔 (ap-¬ε ¬inA ninΓ inΓ apA) (ap-find' fd inΓ ninΓ apA₁)
ap-find' (f-∀ fd) inΓ ninΓ (ap-∀ apA) = f-∀ (ap-find' fd (S∙ inΓ) (S∙ ninΓ) apA)

ap-find0 : find A #0 j
         → Γ% ,∙ ≫ A ⇘ A% -- may need Norm Γ%
         → find A% #0 j
ap-find0 fd apA = ap-find' fd Z Z∙ apA

late-ap-v2 : ∀ {C*%}
           → ⟦ B ⟧ C ⇘ C*
           → Γ% ≫ C* ⇘ C*%
           → Γ% ≫ B ⇘ B%
           → Γ% ,= B% ≫ C ⇘ C%'
           → ↑ty0 C*% ⇘ C%'

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
sound-s (s-∀l {B = B} s ic fd stC stD) apΓ (ap-∀ {A% = A%} apA) (ap-arr apC apD) with s-cloΓ s
... | clo-S= r cloA =
  let ⟨ B%  , apB% ⟩ = ap-total (ap-close-prv cloA apΓ)
      ⟨ A%* , stA% ⟩ = st0-total B% A%
      ⟨ A%*' , apA% ⟩ = ap-total (ap-close-prv (s-cloA s) (ap-S= apΓ apB%))
      ⟨ C%' , apC% ⟩ = ap-total {!!}
      ⟨ D%' , apD% ⟩ = ap-total {!!}
  in s-∀l {B = B%} stA% (sd-strengthen=0 (sound-s s (ap-S= apΓ apB%)
    apA% (ap-arr apC% apD%))
    (late-ap apA stA% apA%) (↑ty-arr (late-ap-v2 stC apC apB% apC%)
                                     (late-ap-v2 stD apD apB% apD%)))
                                     ic
                                     (ap-find0 fd apA)
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
sound (⊢var cloΣ x∈Γ) apΓ apA ap-var = ⊢var (ap-closed cloΣ apΓ) (ap-∋⦂ x∈Γ cloΣ apΓ apA)
sound (⊢ann ⊢e) apΓ apA (ap-ann apA₁ ape) with ap-unique apA apA₁
... | refl = ⊢ann (sound ⊢e apΓ apA ape)
sound (⊢lam₁ ⊢e) apΓ (ap-arr apA apA₁) (ap-lam ape) =
  ⊢lam₁ (sound ⊢e (ap-S, apΓ apA) (ap-weaken,0 apA₁) (ape-invar,0 ape))
sound (⊢lam₂ ⊢e) apΓ (ap-arr apA apA₁) (ap-lam ape) =
  ⊢lam₂ (sound ⊢e (ap-S, apΓ apA) (ap-weaken,0 apA₁) (ape-invar,0 ape))
sound (⊢app₁ ⊢e ⊢e₁) apΓ apA (ap-app ape ape₁) with ap-total (ap-close-prv (t-cloA ⊢e₁) apΓ)
... | ⟨ A%' , ap' ⟩ = ⊢app₁ (sound ⊢e apΓ (ap-arr ap' apA) ape) (sound ⊢e₁ apΓ ap' ape₁)
sound (⊢app₂ ⊢e ⊢e₁) apΓ apA (ap-app ape ape₁)  with ap-total (ap-close-prv (t-cloA ⊢e₁) apΓ)
... | ⟨ A%' , ap' ⟩ = ⊢app₂ (sound ⊢e apΓ (ap-arr ap' apA) ape) (sound ⊢e₁ apΓ ap' ape₁)
sound (⊢sub ⊢e B≤A j≢Z) apΓ apA ape with ap-total (ap-close-prv (t-cloA ⊢e) apΓ)
... | ⟨ A% , ap ⟩ = ⊢sub (sound ⊢e apΓ ap ape) (sound-s B≤A apΓ ap apA) j≢Z
sound (⊢tabs ⊢e) apΓ (ap-∀ apA) (ap-tlam ape) = ⊢tabs (sound ⊢e (ap-S∙ apΓ) apA ape)
