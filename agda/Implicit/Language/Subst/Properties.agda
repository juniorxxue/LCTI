module Implicit.Language.Subst.Properties where

open import Implicit.Language.Base
open import Implicit.Language.Subst.Base
open import Implicit.Language.Shift

private variable
  k X : Fin m
  A T A' B B₁ B₂ : Type m

st-unique :
    ⟦ k / A ⟧ B ⇘ B₁
  → ⟦ k / A ⟧ B ⇘ B₂
  → B₁ ≡ B₂
st-unique st-int st-int = refl
st-unique st-var st-var = refl
st-unique (st-arr st1 st3) (st-arr st2 st4) rewrite st-unique st1 st2 | st-unique st3 st4 = refl
st-unique (st-∀ up st1) (st-∀ up₁ st2) rewrite ↑ty-unique up up₁ | st-unique st1 st2 = refl

st0-unique :
    ⟦ A ⟧ B ⇘ B₁
  → ⟦ A ⟧ B ⇘ B₂
  → B₁ ≡ B₂
st0-unique st1 st2 = st-unique st1 st2

↑ty-stx :
  ‶ X ≡ ⟦ k / T ⟧ˣ (punchIn k X)
↑ty-stx {X = X} {k = k} with k #≟ (punchIn k X)
... | yes p = ⊥-elim ((punchInᵢ≢i k X) (sym p))
... | no ¬p = cong ‶_ (sym (punchOut-punchIn k))

↑ty-st-eq :
  A ↑ty k ⇘ A'
  → ⟦ k / T ⟧ A' ⇘ B
  → A ≡ B
↑ty-st-eq ↑ty-int st-int = refl
↑ty-st-eq {k = k} (↑ty-var {X = X}) st-var = ↑ty-stx {X = X} {k = k}
↑ty-st-eq (↑ty-arr up up₁) (st-arr st st₁) rewrite ↑ty-st-eq up st | ↑ty-st-eq up₁ st₁ = refl
↑ty-st-eq (↑ty-∀ up) (st-∀ up₁ st) = cong `∀_ (↑ty-st-eq up st)


