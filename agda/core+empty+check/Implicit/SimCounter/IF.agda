module Implicit.SimCounter.IF where

open import Implicit.Language.All
open import Implicit.SimCounter.Typing
open import Implicit.SimCounter.Subtyping

infix 3 _⊢_𝕄_
data _⊢_𝕄_ : Env n m → Type m → Type m → Set where
  𝕄-arr : Γ ⊢ A `→ B 𝕄 A `→ B
  M-∀ : Γ ⊢r T
      → (st : ⟦ T ⟧ A ⇘ A*)
      → Γ ⊢ A* 𝕄 B `→ C
      → Γ ⊢ `∀ A 𝕄 B `→ C

infix 3 _⊢_⦂_⟶_
data _⊢_⦂_⟶_ : Env n m → Term n m → Type m → Term n m → Set where

  ela-lit : (regΓ : TRegular Γ)
          → Γ ⊢ (lit n) ⦂ Int ⟶ (lit n)
  ela-var : (regΓ : TRegular Γ)
          → Γ ∋ x ⦂ A
          → Γ ⊢ ` x ⦂ A ⟶ ` x
  ela-lam : Γ , A ⊢ e ⦂ B ⟶ e'
          → Γ ⊢ ƛ e ⦂ A `→ B ⟶ ƛ e'
  ela-app : Γ ⊢ e₁ ⦂ A ⟶ e₁'
           → Γ ⊢ A 𝕄 B `→ C
           → Γ ⊢ e₂ ⦂ B ⟶ e₂'
           → Γ ⊢ e₁ · e₂ ⦂ C ⟶ e₁' · (e₂' ⦂ B)
  -- two extra rules
  ela-∀i  : Γ ,∙ ⊢ e' ⦂ A ⟶ e₁
         → (upe : ↑tyᵉ0 e ⇘ e')
         → Γ ⊢ e ⦂ `∀ A ⟶ Λ (e₁ ⦂ A)
  ela-∀e  : Γ ⊢ e ⦂ `∀ A ⟶ e'
          → ⟦ B ⟧ A ⇘ A*
          → Γ ⊢r B
          → Γ ⊢ e ⦂ A* ⟶ e' ⓪ B


annotatability : Γ ⊢ e ⦂ A ⟶ e'
               → Γ ⊨ ∞ # e' ⦂ A
annotatability (ela-lit regΓ) = ⊨sub (⊨lit regΓ) (s-int (reg-Z regΓ)) gc-i nz-∞
annotatability (ela-var regΓ x) = {!!}
annotatability (ela-lam ⊢e) = ⊨lam₁ (annotatability ⊢e)
annotatability (ela-app ⊢e x ⊢e₁) = {!!}
annotatability (ela-∀i ⊢e upe) = {!!}
annotatability (ela-∀e ⊢e x x₁) = ⊨tapp {!!} x

private variable
  𝕞 : SCounter

infix 3 _R_by_
data _R_by_ : SCounter → SCounter → Type m → Set where
  R-base : ∞ R 𝕥 ∞ by `∀ A
  R-C    : 𝕟 R 𝕞 by B
         → 𝕔 𝕟 R 𝕔 𝕞 by A `→ B
  R-I    : 𝕟 R 𝕞 by B
         → 𝕚 𝕟 R 𝕚 𝕞 by A `→ B
  R-T    : 𝕟 R 𝕞 by A*
         → ⟦ B ⟧ A ⇘ A*
         → 𝕥 𝕟 R 𝕥 𝕞 by `∀ A


R-s-prv : Γ ⊨ 𝕟 # A ≤ B
        → 𝕟 R 𝕞 by B
        → Γ ⊨ 𝕞 # A ≤ B
R-s-prv (s-arr₂ s s₁) (R-I nm) = s-arr₂ s (R-s-prv s₁ nm)
R-s-prv (s-arr₃ regA s) (R-C nm) = s-arr₃ regA (R-s-prv s nm)
R-s-prv (s-∀ s) R-base = s-tapp s
R-s-prv (s-∀l regB st s ic fd) (R-C nm) = s-∀l regB st (R-s-prv s (R-C nm)) case-𝕔 {!!}
R-s-prv (s-∀l regB st s ic fd) (R-I nm) = s-∀l regB st (R-s-prv s (R-I nm)) case-𝕚 {!!}
R-s-prv (s-∀l-no-appear regB st s ic fd) nm = s-∀l-no-appear regB st (R-s-prv s nm) ic fd
R-s-prv (s-tapp s) (R-T nm x) = s-tapp (R-s-prv s {!!})

R-prv : Γ ⊨ 𝕟 # e ⦂ A
      → 𝕟 R 𝕞 by A
      → Γ ⊨ 𝕞 # e ⦂ A
R-prv (⊨lam₂ ⊢e) (R-I rr) = ⊨lam₂ (R-prv ⊢e rr)
R-prv (⊨app₁ ⊢e ⊢e₁) rr = ⊨app₁ (R-prv ⊢e (R-C rr)) ⊢e₁
R-prv (⊨app₂ ⊢e ⊢e₁) rr = ⊨app₂ (R-prv ⊢e (R-I rr)) ⊢e₁
R-prv (⊨sub ⊢e B≤A gc 𝕟≢Z) rr = ⊨sub ⊢e (R-s-prv B≤A rr) gc {!!}
R-prv (⊨tapp ⊢e st) rr = ⊨tapp (R-prv ⊢e (R-T rr st)) st
