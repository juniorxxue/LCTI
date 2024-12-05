module Implicit.Language.Subst.Properties where

open import Implicit.Language.Base
open import Implicit.Language.Subst.Base
open import Implicit.Language.Shift

private variable
  k X : Fin m
  A T A' B B₁ B₂ B* : Type m
  e e' e* : Term n m

st-unique :
    ⟦ k / A ⟧ B ⇘ B₁
  → ⟦ k / A ⟧ B ⇘ B₂
  → B₁ ≡ B₂
st-unique st-int st-int = refl
st-unique st-var st-var = refl
st-unique (st-arr st1 st3) (st-arr st2 st4) rewrite st-unique st1 st2 | st-unique st3 st4 = refl
st-unique (st-∀ up st1) (st-∀ up₁ st2) rewrite ↑ty-unique up up₁ | st-unique st1 st2 = refl

postulate
  st-total : ∀ (A : Type m) k B → ∃[ B* ](⟦ k / A ⟧ B ⇘ B*)
  st0-total : ∀ (A : Type m) B → ∃[ B* ](⟦ A ⟧ B ⇘ B*)


st0-unique :
    ⟦ A ⟧ B ⇘ B₁
  → ⟦ A ⟧ B ⇘ B₂
  → B₁ ≡ B₂
st0-unique st1 st2 = st-unique st1 st2

↑ty-stx-eq :
  ‶ X ≡ ⟦ k / T ⟧ˣ (punchIn k X)
↑ty-stx-eq {X = X} {k = k} with k #≟ (punchIn k X)
... | yes p = ⊥-elim ((punchInᵢ≢i k X) (sym p))
... | no ¬p = cong ‶_ (sym (punchOut-punchIn k))

↑ty-st-eq :
    A ↑ty k ⇘ A'
  → ⟦ k / T ⟧ A' ⇘ B
  → A ≡ B
↑ty-st-eq ↑ty-int st-int = refl
↑ty-st-eq {k = k} (↑ty-var {X = X}) st-var = ↑ty-stx-eq {X = X} {k = k}
↑ty-st-eq (↑ty-arr up up₁) (st-arr st st₁) rewrite ↑ty-st-eq up st | ↑ty-st-eq up₁ st₁ = refl
↑ty-st-eq (↑ty-∀ up) (st-∀ up₁ st) = cong `∀_ (↑ty-st-eq up st)

↑ty-st :
    A ↑ty k ⇘ A'
  → ⟦ k / T ⟧ A' ⇘ A
↑ty-st ↑ty-int = st-int
↑ty-st {k = k} {T = T} (↑ty-var {X = X}) rewrite ↑ty-stx-eq {X = X} {k = k} {T = T} = st-var
↑ty-st (↑ty-arr up up₁) = st-arr (↑ty-st up) (↑ty-st up₁)
↑ty-st {T = T} (↑ty-∀ up) with ↑ty-total T #0
... | ⟨ _ , up' ⟩ = st-∀ up' (↑ty-st up)

{-
-- this is a wrong lemma, T is Int, k is 0, A' is 0
st-↑ty : ⟦ k / T ⟧ A' ⇘ A
       → A ↑ty k ⇘ A'
st-↑ty st-int = ↑ty-int
st-↑ty {k = k} {T = T} (st-var {X = X}) = {!!}
st-↑ty (st-arr st st₁) = ↑ty-arr (st-↑ty st) (st-↑ty st₁)
st-↑ty (st-∀ up st) = ↑ty-∀ (st-↑ty st)
-}

↑tyᵉ-st-eq :
    e ↑tyᵉ k ⇘ e'
  → ⟦ k / T ⟧ᵉ e' ⇘ e*
  → e ≡ e*
↑tyᵉ-st-eq ↑tyᵉ-lit st-lit = refl
↑tyᵉ-st-eq ↑tyᵉ-var st-var = refl
↑tyᵉ-st-eq (↑tyᵉ-ƛ up) (st-ƛ st) = cong ƛ_ (↑tyᵉ-st-eq up st)
↑tyᵉ-st-eq (↑tyᵉ-app up up₁) (st-· st st₁) rewrite ↑tyᵉ-st-eq up st | ↑tyᵉ-st-eq up₁ st₁ = refl
↑tyᵉ-st-eq (↑tyᵉ-⦂ up x) (st-⦂ st x₁) rewrite ↑tyᵉ-st-eq up st | ↑ty-st-eq x x₁ = refl
↑tyᵉ-st-eq (↑tyᵉ-Λ up) (st-Λ st) = cong Λ_ (↑tyᵉ-st-eq up st)

↑tyᵉ-st :
    e ↑tyᵉ k ⇘ e'
  → ⟦ k / T ⟧ᵉ e' ⇘ e
↑tyᵉ-st ↑tyᵉ-lit = st-lit
↑tyᵉ-st ↑tyᵉ-var = st-var
↑tyᵉ-st (↑tyᵉ-ƛ up) = st-ƛ (↑tyᵉ-st up)
↑tyᵉ-st (↑tyᵉ-app up up₁) = st-· (↑tyᵉ-st up) (↑tyᵉ-st up₁)
↑tyᵉ-st (↑tyᵉ-⦂ up up₁) = st-⦂ (↑tyᵉ-st up) (↑ty-st up₁)
↑tyᵉ-st (↑tyᵉ-Λ up) = st-Λ (↑tyᵉ-st up)

st-total-rev : ∀ k B → ∃[ A ](⟦ k / T ⟧ A ⇘ B)
st-total-rev k B = let ⟨ B* , up ⟩ = ↑ty-total B k in ⟨ B* , ↑ty-st up ⟩

st0-total-rev : ∀ B → ∃[ A ](⟦ T ⟧ A ⇘ B)
st0-total-rev = st-total-rev #0
