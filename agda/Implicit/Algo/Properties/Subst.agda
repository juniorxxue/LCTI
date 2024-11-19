module Implicit.Algo.Properties.Subst where

open import Implicit.Language
open import Implicit.Algo.Base

private variable
  Σ Σ' Σ* : Context n m
  k : Fin m
  T : Type m

↑tyᶜ-st-eq :
    Σ ↑tyᶜ k ⇘ Σ'
  → ⟦ k / T ⟧ᶜ Σ' ⇘ Σ*
  → Σ ≡ Σ*
↑tyᶜ-st-eq ↑tyᶜ-□ empty = refl
↑tyᶜ-st-eq (↑tyᶜ-τ x) (fulltype st) rewrite ↑ty-st-eq x st = refl
↑tyᶜ-st-eq (↑tyᶜ-e up-e up-c) (term st-c st-e) rewrite ↑tyᶜ-st-eq up-c st-c | ↑tyᵉ-st-eq up-e st-e = refl

↑tyᶜ-st :
    Σ ↑tyᶜ k ⇘ Σ'
  → ⟦ k / T ⟧ᶜ Σ' ⇘ Σ
↑tyᶜ-st ↑tyᶜ-□ = empty
↑tyᶜ-st (↑tyᶜ-τ up-t) = fulltype (↑ty-st up-t)
↑tyᶜ-st (↑tyᶜ-e up-e up) = term (↑tyᶜ-st up) (↑tyᵉ-st up-e)

