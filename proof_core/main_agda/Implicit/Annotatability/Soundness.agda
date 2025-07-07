module Implicit.Annotatability.Soundness where

open import Implicit.Language.All
open import Implicit.Decl.Typing
open import Implicit.Decl.Subtyping

data IFTerm : ℕ → Set where
  lit      : (i : ℕ) → IFTerm n
  `_       : (x : Fin n) → IFTerm n
  ƛ_       : (e : IFTerm (1 + n)) → IFTerm n
  _·_      : (e₁ : IFTerm n) → (e₂ : IFTerm n) → IFTerm n


private variable
  M M' N N' J K P : IFTerm n

infix 3 _⊢_⊑_
data _⊢_⊑_ : Env n m → Type m → Type m → Set where
  if-refl : Γ ⊢ A ⊑ A
  if-∀L : ⟦ C ⟧ A ⇘ A*
         → Γ ⊢r T
         → Γ ⊢ A* ⊑ B
         → Γ ⊢ `∀ A ⊑ B
  if-∀R : Γ ,∙ ⊢ A' ⊑ B
          → (up : ↑ty0 A ⇘ A')
          → Γ ⊢ A ⊑ `∀ B
  if-arr : Γ ⊢ C ⊑ A
          → Γ ⊢ B ⊑ D
          → Γ ⊢ A `→ B ⊑ C `→ D
  if-∀ : Γ ,∙ ⊢ A ⊑ B
        → Γ ⊢ `∀ A ⊑ `∀ B
  if-trans : Γ ⊢ A ⊑ B
            → Γ ⊢ B ⊑ C
            → Γ ⊢ A ⊑ C


infix 3 _⊢_⦂_
data _⊢_⦂_ : Env n m → IFTerm n → Type m → Set where

  ela-lit : (regΓ : TRegular Γ)
          → Γ ⊢ (lit n) ⦂ Int
  ela-var : (regΓ : TRegular Γ)
          → Γ ∋ x ⦂ A
          → Γ ⊢ ` x ⦂ A
  ela-lam : Γ , A ⊢ M ⦂ B
          → Γ ⊢ ƛ M ⦂ A `→ B
  ela-app : Γ ⊢ M ⦂ A `→ B
           → Γ ⊢ N ⦂ A
           → Γ ⊢ M · N ⦂ B
  ela-∀i : Γ ,∙ ⊢ M ⦂ A
         → Γ ⊢ M ⦂ `∀ A
  ela-sub : Γ ⊢ M ⦂ A
          → Γ ⋈ ⊢ A ⊑ B
          → Γ ⊢ M ⦂ B

data Erasure : Term n m → IFTerm n → Set where
  era-lit : ∀ {i} → Erasure (Term n m ∋⦂ (lit i)) (lit i)
  era-var : Erasure (Term n m ∋⦂ (` x)) (` x)
  era-lam : Erasure e M → Erasure (ƛ e) (ƛ M)
  era-app : Erasure e₁ M → Erasure e₂ N → Erasure (e₁ · e₂) (M · N)
  era-ann : Erasure e M → Erasure (e ⦂ A) M
  era-tlam : Erasure e M
           → Erasure (Λ e) M
  era-tapp : Erasure e M
           → Erasure (e ⓪ A) M


s-sound : Γ ⊢ j # A ≤ B
        → Γ ⊢ A ⊑ B
s-sound (s-refl regΔ cloA) = if-refl
s-sound (s-int regΔ) = if-refl
s-sound (s-var-∙ regΔ inΔ) = if-refl
s-sound (s-arr₁ s s₁) = if-arr (s-sound s) (s-sound s₁)
s-sound (s-arr₂ s s₁) = if-arr (s-sound s) (s-sound s₁)
s-sound (s-arr₃ regA s) = if-arr if-refl (s-sound s)
s-sound (s-∀ s) = if-∀ (s-sound s)
s-sound (s-∀l regB st s ic fd upj) = if-∀L st regB (s-sound s)
s-sound (s-∀l-no-appear regB st s ic fd) = if-∀L st regB (s-sound s)
s-sound (s-tapp regB st s upC) = if-∀L st regB (if-trans (s-sound s) (if-∀R if-refl upC))

sound : Γ ⊢ j # e ⦂ A
      → Erasure e M
      → Γ ⊢ M ⦂ A
sound (⊢lit regΓ) era-lit = ela-lit regΓ
sound (⊢var regΓ x∈Γ) era-var = ela-var regΓ x∈Γ
sound (⊢ann ⊢e) (era-ann era) = sound ⊢e era
sound (⊢lam₁ ⊢e) (era-lam era) = ela-lam (sound ⊢e era)
sound (⊢lam₂ ⊢e) (era-lam era) = ela-lam (sound ⊢e era)
sound (⊢app₁ ⊢e ⊢e₁) (era-app era era₁) = ela-app (sound ⊢e era) (sound ⊢e₁ era₁)
sound (⊢app₂ ⊢e ⊢e₁) (era-app era era₁) = ela-app (sound ⊢e era) (sound ⊢e₁ era₁)
sound (⊢sub ⊢e B≤A gc j≢Z) era = ela-sub (sound ⊢e era) (s-sound B≤A)
sound (⊢tabs ⊢e) (era-tlam era) = ela-∀i (sound ⊢e era)
sound (⊢tabs-∞ ⊢e) (era-tlam era) = ela-∀i (sound ⊢e era)
sound (⊢tapp ⊢e st) (era-tapp era) = ela-sub (sound ⊢e era) (if-∀L st ⊢r-int if-refl)
