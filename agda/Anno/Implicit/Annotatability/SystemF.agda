module Implicit.Annotatability.SystemF where

open import Implicit.Language.All
open import Implicit.Decl.Typing
open import Implicit.Decl.Subtyping

private variable
  e₁′ : Term n m

infix 3 _𝕄_
data _𝕄_ : Type m → Type m → Set where

  𝕄-arr : A `→ B 𝕄 A `→ B
  M-∀ : (st : ⟦ T ⟧ A ⇘ A*)
       → A* 𝕄 B `→ C
       → (ocr : #0 ε A)
       → `∀ A 𝕄 B `→ C

infix 3 _⊢_⦂_⟶_
data _⊢_⦂_⟶_ : Env n m → Term n m → Type m → Term n m → Set where

  ela-lit : Γ ⊢ (lit n) ⦂ Int ⟶ (lit n)
  ela-var : Γ ∋ x ⦂ A
          → Γ ⊢ ` x ⦂ A ⟶ ` x
  ela-lam : Γ , A ⊢ e ⦂ B ⟶ e'
          → Γ ⊢ ƛ e ⦂ A `→ B ⟶ ƛ e'
  ela-app : Γ ⊢ e₁ ⦂ A ⟶ e₁'
           → A 𝕄 B `→ C
           → Γ ⊢ e₂ ⦂ B ⟶ e₂'
           → Γ ⊢ e₁ · e₂ ⦂ C ⟶ e₁' · (e₂' ⦂ B)

infix 3 _⟾_
data _⟾_ : Counter m × Type m → Counter m × Type m → Set where
  base : A 𝕄 B
       → ⟨ ∞ , A ⟩ ⟾ ⟨ 𝕚 ∞ , B ⟩
  case-𝕚 : ⟨ j , B ⟩ ⟾ ⟨ j' , D ⟩
         → ⟨ 𝕚 j , A `→ B ⟩ ⟾ ⟨ 𝕚 j' , A `→ D ⟩
  case-𝕔 : ⟨ j , B ⟩ ⟾ ⟨ j' , D ⟩
         → ⟨ 𝕔 j , A `→ B ⟩ ⟾ ⟨ 𝕔 j' , A `→ D ⟩
  case-𝕥 : ⟨ j′ , B ⟩ ⟾ ⟨ j″ , D ⟩
         → (upj1 : ↑tyʲ0 j ⇘ j′)
         → (upj2 : ↑tyʲ0 j' ⇘ j″)
         → ⟨ 𝕥₍ A ₎ j , `∀ B ⟩ ⟾ ⟨ 𝕥₍ A ₎ j' , `∀ D ⟩


conv-sub-gen-s : Γ ⊢ j # A ≤ B
               → ⟨ j , B ⟩ ⟾ ⟨ j' , C ⟩
               → Γ ⊢ j' # A ≤ C  --- we need to generalize the conclusion
conv-sub-gen-s (s-int regΔ) (base ())
conv-sub-gen-s (s-var-∙ regΔ inΔ) (base ())
conv-sub-gen-s (s-arr₁ s s₁) (base 𝕄-arr) = s-arr₂ s s₁
conv-sub-gen-s (s-arr₂ s s₁) (case-𝕚 cv) = s-arr₂ s (conv-sub-gen-s s₁ cv)
conv-sub-gen-s (s-arr₃ regA s) (case-𝕔 cv) = s-arr₃ regA (conv-sub-gen-s s cv)
conv-sub-gen-s (s-∀ s) (base (M-∀ st mm ocr)) = {!!}
-- conv-sub-gen-s (s-∀ s) (base (M-∀ {T = T} x x₁ ocr))
--  with refl ← s-trans-∞-eq s = s-∀l {B = T} {!!} x {!!} case-𝕚 {!!} (↑tyʲ-𝕚 ↑tyʲ-∞) -- some inductive happens here
conv-sub-gen-s (s-∀l regB st s case-𝕚 fd upj) (case-𝕚 cv) = s-∀l regB st (conv-sub-gen-s s (case-𝕚 cv)) case-𝕚 {!!} {!!} -- ok
conv-sub-gen-s (s-∀l regB st s case-𝕔 fd upj) (case-𝕔 cv) = s-∀l regB st (conv-sub-gen-s s (case-𝕔 cv)) case-𝕔 {!!} {!!} -- ok
conv-sub-gen-s (s-tapp regB st s upC) (case-𝕥 cv upj1 upj2) = s-tapp regB st (conv-sub-gen-s s {!cv!}) {!!}  -- ok

conv-sub-gen : Γ ⊢ j # e ⦂ A
             → ⟨ j , A ⟩ ⟾ ⟨ j' , B ⟩
             → Γ ⊢ j' # e ⦂ B
conv-sub-gen (⊢lam₁ ⊢e) (base 𝕄-arr) = ⊢lam₂ ⊢e
conv-sub-gen (⊢lam₂ ⊢e) (case-𝕚 cv) = ⊢lam₂ (conv-sub-gen ⊢e cv)
conv-sub-gen (⊢app₁ ⊢e ⊢e₁) cv = ⊢app₁ (conv-sub-gen ⊢e (case-𝕔 cv)) ⊢e₁
conv-sub-gen (⊢app₂ ⊢e ⊢e₁) cv = ⊢app₂ (conv-sub-gen ⊢e (case-𝕚 cv)) ⊢e₁
conv-sub-gen (⊢sub ⊢e B≤A gc j≢Z) cv = ⊢sub ⊢e (conv-sub-gen-s B≤A cv) gc {!!} -- ok
conv-sub-gen (⊢tapp ⊢e st) cv = ⊢tapp (conv-sub-gen ⊢e (case-𝕥 {!!} {!!} {!!})) {!!} -- could be avoided

conv-sub : Γ ⊢ ∞ # e ⦂ A
         → A 𝕄 B
         → Γ ⊢ 𝕚 ∞ # e ⦂ B
-- conv-sub ⊢e cv = conv-sub-gen ⊢e (base cv)
conv-sub (⊢lam₁ ⊢e) 𝕄-arr = ⊢lam₂ ⊢e
conv-sub (⊢app₁ ⊢e ⊢e₁) cv = ⊢app₁ {!!} ⊢e₁
conv-sub (⊢app₂ ⊢e ⊢e₁) cv = ⊢app₂ {!!} ⊢e₁
conv-sub (⊢sub ⊢e B≤A gc j≢Z) cv = ⊢sub ⊢e {!!} gc nz-I
conv-sub (⊢tapp ⊢e st) cv = ⊢tapp {!!} {!!}

annotatability : Γ ⊢ e ⦂ A ⟶ e'
               → Γ ⊢ ∞ # e' ⦂ A
annotatability ela-lit = ⊢sub (⊢lit {!!}) {!!} gc-i nz-∞
annotatability (ela-var x) = {!!}
annotatability (ela-lam ⊢e) = ⊢lam₁ (annotatability ⊢e)
annotatability (ela-app ⊢e cv ⊢e₁) = ⊢app₂ (conv-sub (annotatability ⊢e) cv) (⊢ann (annotatability ⊢e₁))
