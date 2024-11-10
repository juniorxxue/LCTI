module Implicit.Properties where

open import Implicit.Common


postulate
  ↑ty-st-var : ∀ {k : Fin (1 + m)} {X B C}
    → [ k / C ]ˢ ‶ punchIn k X ⇘ B
    → ‶ X ≡ B
-- ↑ty-st-var {k = #0} {X} (st-var-neq ¬p) = refl
-- ↑ty-st-var {k = #S k} {#0} (st-var-neq ¬p) = refl
-- ↑ty-st-var {k = #S k} {#S X} st = {!!}

↑ty-st : ∀ {A : Type m} {k C B}
  → [ k / C ]ˢ (↑ty k A) ⇘ B
  → A ≡ B
↑ty-st {A = Int} st-int = refl
↑ty-st {A = ‶ X} {k} st = ↑ty-st-var st
↑ty-st {A = D `→ E} (st-arr st st₁) rewrite ↑ty-st {A = D} st | ↑ty-st {A = E} st₁ = refl
↑ty-st {A = `∀ A} (st-∀ up₁ st) = cong `∀_ (↑ty-st {A = A} st)

postulate
  ↑ty-st' : ∀ (A : Type m) {C}
    → [ C ]ˢ (↑ty0 A) ≡ A
    
  ↑ty-tm-st' : ∀ (e : Term n m) {C}
    → [ C ]ᵗ (↑ty0-tm e) ≡ e

  ↑ty-st⇘ : ∀ {A : Type m}{C}
    → [ C ]ˢ (↑ty0 A) ⇘ A

  ↑ty⇘-st : ∀ {A : Type m}{A' C}
    → ↑ty0 A ⇘ A'
    → [ C ]ˢ A' ≡ A

ty-ty-gen : ∀ {A : Type m} {A' k}
  → ty A ↑ k ⇘ A'
  → ↑ty k A ≡ A'
ty-ty-gen ↑int = refl
ty-ty-gen ↑var = refl
ty-ty-gen (↑arr sf sf₁) rewrite ty-ty-gen sf | ty-ty-gen sf₁ = refl
ty-ty-gen (↑∀ sf) rewrite ty-ty-gen sf = refl

st-st-gen : ∀ {A : Type (1 + m)} {B A' k}
  → [ k / B ]ˢ A ⇘ A'
  → [ k / B ]ˢ A ≡ A'
st-st-gen st-int = refl
st-st-gen {k = k} st-var-eq with k #≟ k
... | yes p = refl
... | no ¬p = ⊥-elim (¬p refl)
st-st-gen {k = k} (st-var-neq {X = X} ¬p) with  k #≟ X
... | yes p = ⊥-elim (¬p p)
... | no ¬p = refl
st-st-gen (st-arr st st₁) rewrite st-st-gen st | st-st-gen st₁ = refl
st-st-gen (st-∀ up₁ st) rewrite ty-ty-gen up₁ | st-st-gen st = refl
  
st-st : ∀ {A : Type (1 + m)} {B A'}
  → [ B ]ˢ A ⇘ A'
  → [ B ]ˢ A ≡ A'
st-st st = st-st-gen st
