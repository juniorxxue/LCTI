module Implicit.DeclNew.Main where

open import Implicit.Language.All
open import Implicit.Decl.All

infix 3 _⊢n_#_≤_
data _⊢n_#_≤_ : Env n m → Counter m → Type m → Type m → Set where
  s-refl :
      (regΔ : SRegular Δ)
    → (cloA : Δ ⊢r A)
    → Δ ⊢n Z # A ≤ A
  s-int :
      (regΔ : SRegular Δ)
    → Δ ⊢n ∞ # Int ≤ Int
  s-var-∙ :
      (regΔ : SRegular Δ)
    → (inΔ : Δ ∋∙ X)
    → Δ ⊢n ∞ # ‶ X ≤ ‶ X
  s-arr₁ :
      Δ ⊢n ∞ # C ≤ A
    → Δ ⊢n ∞ # B ≤ D
    → Δ ⊢n ∞ # A `→ B ≤ C `→ D
  s-arr₂ :
      Δ ⊢n ∞ # C ≤ A
    → Δ ⊢n j # B ≤ D
    → Δ ⊢n 𝕚 j # A `→ B ≤ C `→ D
  s-arr₃ :
      (regA : Δ ⊢r A)
    → Δ ⊢n j # B ≤ D
    → Δ ⊢n 𝕔 j # A `→ B ≤ A `→ D
  s-∀ :
      Δ ,∙ ⊢n ∞ # A ≤ B
    → Δ ⊢n ∞ # `∀ A ≤ `∀ B
  s-∀l :
      (regB : Γ ⊢r B)
    → (st : ⟦ B ⟧ A ⇘ A*)
    → Γ ⊢n j # A* ≤ C `→ D
    → (ic : (𝕚𝕔 j))
    → (fd : find A #0 j')
    → (upj : ↑tyʲ0 j ⇘ j')
    → Γ ⊢n j # `∀ A ≤ C `→ D
  s-∀l-no-appear :
      (regB : Γ ⊢r B)
    → (st : ⟦ B ⟧ A ⇘ A*)
    → Γ ⊢n j # A* ≤ C `→ D
    → (ic : (𝕚𝕔 j))
    → (fd : #0 ¬ε A)
    → Γ ⊢n j # `∀ A ≤ C `→ D


infix 3 _⊢n_#_⦂_
data _⊢n_#_⦂_ : Env n m → Counter m → Term n m → Type m → Set where
  ⊢lit : ∀ {num : ℕ}
    → (regΓ : TRegular Γ)
    → Γ ⊢n Z # (lit num) ⦂ Int
  ⊢var :
      (regΓ : TRegular Γ)
    → (x∈Γ : Γ ∋ x ⦂ A)
    → Γ ⊢n Z # ` x ⦂ A
  ⊢ann :
      Γ ⊢n ∞ # e ⦂ A
    → Γ ⊢n Z # (e ⦂ A) ⦂ A
  ⊢lam₁ :
      Γ , A ⊢n ∞ # e ⦂ B
    → Γ ⊢n ∞ # ƛ e ⦂ A `→ B
  ⊢lam₂ :
      Γ , A ⊢n j # e ⦂ B
    → Γ ⊢n 𝕚 j # ƛ e ⦂ A `→ B
  ⊢app₁ :
      Γ ⊢n 𝕔 j # e₁ ⦂ A `→ B
    → Γ ⊢n ∞ # e₂ ⦂ A
    → Γ ⊢n j # e₁ · e₂ ⦂ B
  ⊢app₂ :
      Γ ⊢n 𝕚 j # e₁ ⦂ A `→ B
    → Γ ⊢n Z # e₂ ⦂ A
    → Γ ⊢n j # e₁ · e₂ ⦂ B
  ⊢sub :
      Γ ⊢n Z # g ⦂ A
   → (B≤A : Γ ⋈ ⊢n j # A ≤ B)
    → (gc : GenericConsumer g)
    → (j≢Z : NonZ j)
    → Γ ⊢n j # g ⦂ B
  ⊢tabs :
      Γ ,∙ ⊢n Z # e ⦂ A
    → Γ ⊢n Z # Λ e ⦂ `∀ A
  ⊢tabs-∞ :
      Γ ,∙ ⊢n ∞ # e ⦂ A
    → Γ ⊢n ∞ # Λ e ⦂ `∀ A
  ⊢tapp :
      Γ ⊢n Z # e ⦂ `∀ B
    → (st : ⟦ A ⟧ B ⇘ B*)
   → (regA : Γ ⊢r A)
   → (B≤A : Γ ⋈ ⊢n j # B* ≤ C)
    → Γ ⊢n j # e ⓪ A ⦂ C

sound-s : Γ ⊢n j # A ≤ B
        → Γ ⊢d j # A ≤ B
sound-s (s-refl regΔ cloA) = s-refl regΔ cloA
sound-s (s-int regΔ) = s-int regΔ
sound-s (s-var-∙ regΔ inΔ) = s-var-∙ regΔ inΔ
sound-s (s-arr₁ s s₁) = s-arr₁ (sound-s s) (sound-s s₁)
sound-s (s-arr₂ s s₁) = s-arr₂ (sound-s s) (sound-s s₁)
sound-s (s-arr₃ regA s) = s-arr₃ regA (sound-s s)
sound-s (s-∀ s) = s-∀ (sound-s s)
sound-s (s-∀l regB st s ic fd upj) = s-∀l regB st (sound-s s) ic fd upj
sound-s (s-∀l-no-appear regB st s ic fd) = s-∀l-no-appear regB st (sound-s s) ic fd

sound : Γ ⊢n j # e ⦂ A
      → Γ ⊢d j # e ⦂ A
sound (⊢lit regΓ) = ⊢lit regΓ
sound (⊢var regΓ x∈Γ) = ⊢var regΓ x∈Γ
sound (⊢ann ⊢e) = ⊢ann (sound ⊢e)
sound (⊢lam₁ ⊢e) = ⊢lam₁ (sound ⊢e)
sound (⊢lam₂ ⊢e) = ⊢lam₂ (sound ⊢e)
sound (⊢app₁ ⊢e ⊢e₁) = ⊢app₁ (sound ⊢e) (sound ⊢e₁)
sound (⊢app₂ ⊢e ⊢e₁) = ⊢app₂ (sound ⊢e) (sound ⊢e₁)
sound (⊢sub ⊢e B≤A gc j≢Z) = ⊢sub (sound ⊢e) (sound-s B≤A) gc j≢Z
sound (⊢tabs ⊢e) = ⊢tabs (sound ⊢e)
sound (⊢tabs-∞ ⊢e) = ⊢tabs-∞ (sound ⊢e)
sound (⊢tapp {C = C} ⊢e st regA B≤A)
  with ⟨ C' , upC ⟩ ← ↑ty0-total C
  = ⊢tapp (gen-sub (sound ⊢e) Z≋ (s-tapp (⊢r-𝕣 regA) st (sound-s B≤A) upC)) (↑ty-st upC)



complete1 : Γ ⊢d j # A ≤ B
          → ∃[ T ](j ≢ 𝕥₍ T ₎ j')
         → Γ ⊢n j # A ≤ B

complete2 : Γ ⊢d 𝕥₍ B ₎ j # `∀ A ≤ `∀ C
          → ⟦ B ⟧ A ⇘ A*
          → ⟦ B ⟧ C ⇘ C*
          → Γ ⊢n j # A* ≤ C*


complete1 (s-refl regΔ cloA) neq = s-refl regΔ cloA
complete1 (s-int regΔ) neq = s-int regΔ
complete1 (s-var-∙ regΔ inΔ) neq = s-var-∙ regΔ inΔ
complete1 (s-arr₁ s s₁) neq = {!!}
complete1 (s-arr₂ s s₁) neq = {!!}
complete1 (s-arr₃ regA s) neq = {!!}
complete1 (s-∀ s) neq = {!!}
complete1 (s-∀l regB st s ic fd upj) neq = s-∀l regB st (complete1 s neq) ic fd upj
complete1 (s-∀l-no-appear regB st s ic fd) neq = s-∀l-no-appear regB st (complete1 s neq) ic fd
complete1 (s-tapp regB st s upC) neq = ⊥-elim {!!}
{-
complete (s-refl regΔ cloA) = s-refl regΔ cloA
complete (s-int regΔ) = s-int regΔ
complete (s-var-∙ regΔ inΔ) = s-var-∙ regΔ inΔ
complete (s-arr₁ ⊢e ⊢e₁) = s-arr₁ (complete ⊢e) (complete ⊢e₁)
complete (s-arr₂ ⊢e ⊢e₁) = s-arr₂ (complete ⊢e) (complete ⊢e₁)
complete (s-arr₃ regA ⊢e) = s-arr₃ regA (complete ⊢e)
complete (s-∀ ⊢e) = s-∀ (complete ⊢e)
complete (s-∀l regB st ⊢e ic fd upj) = s-∀l regB st (complete ⊢e) ic fd upj
complete (s-∀l-no-appear regB st ⊢e ic fd) = s-∀l-no-appear regB st (complete ⊢e) ic fd
complete (s-tapp regB st ⊢e upC) = {!!}
-}
