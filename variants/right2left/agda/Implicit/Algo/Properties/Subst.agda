module Implicit.Algo.Properties.Subst where

open import Implicit.Language.All
open import Implicit.Algo.Base

↑tyᶜ-st-eq :
    Σ ↑tyᶜ k ⇘ Σ'
  → ⟦ k / T ⟧ᶜ Σ' ⇘ Σ*
  → Σ ≡ Σ*
↑tyᶜ-st-eq ↑tyᶜ-□ empty = refl
↑tyᶜ-st-eq (↑tyᶜ-τ x) (fulltype st) rewrite ↑ty-st-eq x st = refl
↑tyᶜ-st-eq (↑tyᶜ-e up-e up-c) (term st-c st-e) rewrite ↑tyᶜ-st-eq up-c st-c | ↑tyᵉ-st-eq up-e st-e = refl
↑tyᶜ-st-eq (↑tyᶜ-⓪ upA up) (tapp st-c stA) rewrite ↑tyᶜ-st-eq up st-c | ↑ty-st-eq upA stA = refl

↑tyᶜ-st :
    Σ ↑tyᶜ k ⇘ Σ'
  → ⟦ k / T ⟧ᶜ Σ' ⇘ Σ
↑tyᶜ-st ↑tyᶜ-□ = empty
↑tyᶜ-st (↑tyᶜ-τ up-t) = fulltype (↑ty-st up-t)
↑tyᶜ-st (↑tyᶜ-e up-e up) = term (↑tyᶜ-st up) (↑tyᵉ-st up-e)
↑tyᶜ-st (↑tyᶜ-⓪ x x₁) = tapp (↑tyᶜ-st x₁) (↑ty-st x)
