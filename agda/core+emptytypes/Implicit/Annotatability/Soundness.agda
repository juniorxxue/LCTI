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
  M N J K P : IFTerm n

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


if-weaken∙0 : Γ ⊢ M ⦂ A
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

{-
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
if-sub ⊢e (𝕞-∀ mm up) = ela-∀i (if-weaken∙0 (if-sub ⊢e mm) up)
-}
{-
data Build : IFTerm n → Counter m → Type m → IFTerm n → Type m →  Set where
  bd-z : Build M Z A M A
  bd-∞ : Build M ∞ A M A
  bd-c : Build M j B J C
       → Γ ⊢ N ⦂ A
       → Build M (𝕔 j) (A `→ B) (J · N)
  bd-i : Build M j B J
       → Γ ⊢ N ⦂ A
       → Build M (𝕚 j) (A `→ B) (J · N)
  bd-t : Build M j B J
       → Build M (𝕥₍ T ₎ j) B J

sound-gen : Γ ⊢ j # e ⦂ A
          → Erasure e M
          → Build M j A N
          → Γ ⊢ N ⦂ A
sound-gen (⊢lit regΓ) era-lit bd-z = ela-lit regΓ
sound-gen (⊢var regΓ x∈Γ) era-var bd-z = ela-var regΓ x∈Γ
sound-gen (⊢ann ⊢e) (era-ann era) bd-z = sound-gen ⊢e era bd-∞
sound-gen (⊢lam₁ ⊢e) (era-lam era) bd-∞ = ela-lam (sound-gen ⊢e era bd-∞)
sound-gen (⊢lam₂ ⊢e) (era-lam era) (bd-i bd x) = {!!}
sound-gen (⊢app₁ ⊢e ⊢e₁) era bd = {!!}
sound-gen (⊢app₂ ⊢e ⊢e₁) era bd = {!!}
sound-gen (⊢sub ⊢e B≤A gc j≢Z) era bd = {!!}
sound-gen (⊢tabs ⊢e) era bd = {!!}
sound-gen (⊢tapp ⊢e st) era bd = {!!}
-}

infix 3 _⊢_▻_↪_
data _⊢_▻_↪_ : Env n m → IFTerm n → Counter m × Type m → IFTerm n × Type m → Set where
  ▻Z : Γ ⊢ M ▻ ⟨ Z , A ⟩ ↪ ⟨ M , A ⟩
  ▻∞ : Γ ⊢ M ▻ ⟨ ∞ , A ⟩ ↪ ⟨ M , A ⟩
  ▻I : Γ ⊢ (M · N) ▻ ⟨ j , B ⟩ ↪ ⟨ J , C ⟩
     → Γ ⊢ N ⦂ A
     → Γ ⊢ M ▻ ⟨ 𝕚 j , A `→ B ⟩ ↪ ⟨ J , C ⟩
  ▻C : Γ ⊢ (M · N) ▻ ⟨ j , B ⟩ ↪ ⟨ J , C ⟩
     → Γ ⊢ N ⦂ A
     → Γ ⊢ M ▻ ⟨ 𝕔 j , A `→ B ⟩ ↪ ⟨ J , C ⟩


sound : Γ ⊢ j # e ⦂ A
      → Erasure e M
      → Γ ⊢ M ▻ ⟨ j , A ⟩ ↪ ⟨ N , B ⟩
      → Γ ⊢ N ⦂ B
sound (⊢lit regΓ) era bd = {!!}
sound (⊢var regΓ x∈Γ) era bd = {!!}
sound (⊢ann ⊢e) era bd = {!!}
sound (⊢lam₁ ⊢e) era bd = {!!}
sound (⊢lam₂ ⊢e) (era-lam era) (▻I bd x) = {!sound ⊢e era ?!}
sound (⊢app₁ ⊢e ⊢e₁) (era-app era era₁) bd = sound ⊢e era (▻C bd (sound ⊢e₁ era₁ ▻∞))
sound (⊢app₂ ⊢e ⊢e₁) (era-app era era₁) bd = sound ⊢e era (▻I bd (sound ⊢e₁ era₁ ▻Z))
sound (⊢sub ⊢e B≤A gc j≢Z) era bd = {!sound ⊢e era ▻Z !}
sound (⊢tabs ⊢e) era bd = {!!}
sound (⊢tapp ⊢e st) era bd = {!!}
