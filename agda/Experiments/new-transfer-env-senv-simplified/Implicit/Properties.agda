module Implicit.Properties where

open import Implicit.Common


postulate
  ↑ty-st-var : ∀ {k : Fin (1 + m)} {X B C}
    → [ k / C ]ˢ ‶ punchIn k X ⇨ B
    → ‶ X ≡ B
-- ↑ty-st-var {k = #0} {X} (st-var-neq ¬p) = refl
-- ↑ty-st-var {k = #S k} {#0} (st-var-neq ¬p) = refl
-- ↑ty-st-var {k = #S k} {#S X} st = {!!}

↑ty-st : ∀ {A : Type m} {k C B}
  → [ k / C ]ˢ (↑ty k A) ⇨ B
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

  st-st : ∀ {A : Type (1 + m)} {B A'}
    → [ B ]ˢ A ⇨ A'
    → [ B ]ˢ A ≡ A'
  
