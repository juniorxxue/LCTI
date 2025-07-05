module Implicit.Annotatability.Soundness where

open import Implicit.Language.All
open import Implicit.Decl.Typing
open import Implicit.Decl.Subtyping

infix 3 _⊢_𝕄_
data _⊢_𝕄_ : Env n m → Type m → Type m → Set where
  𝕄-arr : Γ ⊢ A `→ B 𝕄 A `→ B
  M-∀ : Γ ⊢r T
      → (st : ⟦ T ⟧ A ⇘ A*)
      → Γ ⊢ A* 𝕄 B `→ C
      → Γ ⊢ `∀ A 𝕄 B `→ C


data IFTerm : ℕ → Set where
  lit      : (i : ℕ) → IFTerm n
  `_       : (x : Fin n) → IFTerm n
  ƛ_       : (e : IFTerm (1 + n)) → IFTerm n
  _·_      : (e₁ : IFTerm n) → (e₂ : IFTerm n) → IFTerm n


private variable
  M N : IFTerm n

infix 3 _⊢_⦂_
data _⊢_⦂_ : Env n m → IFTerm n → Type m → Set where

  ela-lit : (regΓ : TRegular Γ)
          → Γ ⊢ (lit n) ⦂ Int
  ela-var : (regΓ : TRegular Γ)
          → Γ ∋ x ⦂ A
          → Γ ⊢ ` x ⦂ A
  ela-lam : Γ , A ⊢ M ⦂ B
          → Γ ⊢ ƛ M ⦂ A `→ B
  ela-app : Γ ⊢ M ⦂ A
           → Γ ⊢ A 𝕄 B `→ C
           → Γ ⊢ N ⦂ B
           → Γ ⊢ M · N ⦂ C
  ela-∀i  : Γ ,∙ ⊢ M ⦂ A
         → Γ ⊢ M ⦂ `∀ A
  ela-∀e  : Γ ⊢ M ⦂ `∀ A
          → ⟦ B ⟧ A ⇘ A*
          → Γ ⊢ M ⦂ A*


if-weaken∙0 :
              Γ ⊢ M ⦂ A
            → ↑ty0 A ⇘ A'
            → Γ ,∙ ⊢ M ⦂ A'


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



infix 3 _𝕞_
data _𝕞_ : Type m → Type m → Set where
  𝕞-refl : A 𝕞 A
  𝕞-arr : B 𝕞 C
        → A `→ B 𝕞 A `→ C
  𝕞-subst : A* 𝕞 B
          → ⟦ T ⟧ A ⇘ A*
          → `∀ A 𝕞 B
  𝕞-∀ : `∀ A 𝕞 B
       → (up : ↑ty0 B ⇘ B')
       → `∀ A 𝕞 `∀ B'

s-mm : Γ ⊢ j # A ≤ B
     → A 𝕞 B
s-mm (s-refl regΔ cloA) = 𝕞-refl
s-mm (s-int regΔ) = 𝕞-refl
s-mm (s-var-∙ regΔ inΔ) = 𝕞-refl
s-mm (s-arr₁ s s₁) = {!!}
s-mm (s-arr₂ s s₁) = {!!}
s-mm (s-arr₃ regA s) = 𝕞-arr (s-mm s)
s-mm (s-∀ s) = {!!}
s-mm (s-∀l regB st s ic fd upj) = 𝕞-subst (s-mm s) st
s-mm (s-∀l-no-appear regB st s ic fd) = 𝕞-subst (s-mm s) st
s-mm (s-tapp regB st s upC) = {!!}

if-sub : Γ ⊢ M ⦂ A
       → A 𝕞 B
       → Γ ⊢ M ⦂ B
if-sub ⊢e 𝕞-refl = ⊢e
if-sub ⊢e (𝕞-arr mm) = {!!}
if-sub ⊢e (𝕞-subst mm x) = if-sub (ela-∀e ⊢e x) mm
if-sub ⊢e (𝕞-∀ mm up) = ela-∀i {!if-sub ⊢e mm!}

sound : Γ ⊢ j # e ⦂ A
      → Erasure e M
      → Γ ⊢ M ⦂ A
sound (⊢lit regΓ) era-lit = ela-lit regΓ
sound (⊢var regΓ x∈Γ) era-var = ela-var regΓ x∈Γ
sound (⊢ann ⊢e) (era-ann era) = sound ⊢e era
sound (⊢lam₁ ⊢e) (era-lam era) = ela-lam (sound ⊢e era)
sound (⊢lam₂ ⊢e) (era-lam era) = ela-lam (sound ⊢e era)
sound (⊢app₁ ⊢e ⊢e₁) (era-app era era₁) = ela-app (sound ⊢e era) 𝕄-arr (sound ⊢e₁ era₁)
sound (⊢app₂ ⊢e ⊢e₁) (era-app era era₁) = ela-app (sound ⊢e era) 𝕄-arr (sound ⊢e₁ era₁)
sound (⊢sub ⊢e B≤A gc j≢Z) era = {!sound ⊢e era!}
sound (⊢tabs ⊢e) (era-tlam era) = ela-∀i (sound ⊢e era)
sound (⊢tapp ⊢e st) (era-tapp era) = ela-∀e (sound ⊢e era) st
