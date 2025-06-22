{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --allow-incomplete-matches #-}
module Implicit.Algo.Properties.SubsumptionNew where

open import Implicit.Language.All
open import Implicit.Algo.Base
open import Implicit.Algo.Properties.Shift
open import Implicit.Algo.Properties.Id
open import Implicit.Algo.Properties.Reflexivity
open import Implicit.Algo.Properties.Extension
open import Implicit.Algo.Properties.Regularity
open import Implicit.Algo.Properties.Polarity
open import Implicit.Algo.Properties.StrengthenTVar
open import Implicit.Algo.Properties.StrengthenSVar
open import Implicit.Algo.Properties.StrengthenEVar
open import Implicit.Algo.Properties.Weaken
open import Implicit.Algo.Properties.Irrelevance
open import Implicit.Algo.Properties.SubIrrelevance

infix 3 _≊_by_
data _≊_by_ : Context n m → Context n m → Type m → Set where
  ≋□ : (Context n m ∋⦂ □) ≊ (τ A) by A
  ≊S : Σ ≊ Σ' by B
     → [ e ]↝ Σ ≊ [ e ]↝ Σ' by A `→ B
  ≊⓪ : Σ ≊ Σ' by B*
     → ⟦ A ⟧ B ⇘ B*
     → A ⓪↝ Σ ≊ A ⓪↝ Σ' by `∀ B

s-subsumtion : Γ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B
             → Σ ≊ Σ' by B
             → Γ ⊢ A ≤⁺ Σ' ⊣ Δ ↪ B
s-subsumtion (s-empty regΓ cloA grd) ≋□ = s-type {!!}
s-subsumtion (s-term-c ap ⊢e s) (≊S new) = s-term-c ap ⊢e (s-subsumtion s new)
s-subsumtion (s-term-c-n s ap ⊢e) (≊S new) = s-term-c-n (s-subsumtion s new) ap ⊢e
s-subsumtion (s-term-o ⊢e ss s) (≊S new) = s-term-o ⊢e ss (s-subsumtion s new)
s-subsumtion (s-term-o-n s ⊢e ss) (≊S new) = s-term-o-n (s-subsumtion s new) ⊢e ss
s-subsumtion (s-∀l s upᶜ upᵉ upC upD) new = {!!}
s-subsumtion (s-∀l-no s upᶜ upᵉ upC upD) new = {!!}
s-subsumtion (s-tapp s upᶜ) (≊⓪ new x) = s-tapp (s-subsumtion s {!!}) {!!}
s-subsumtion (s-svar-term x s) (≊S new) = s-svar-term x (s-subsumtion s (≊S new))
s-subsumtion (s-svar-tapp x s) (≊⓪ new x₁) = s-svar-tapp x (s-subsumtion s (≊⓪ new x₁))
s-subsumtion (s-evar-infers infs inst) (≊S new) = {!!}

subsumption : Γ ⊢ Σ ⇒ e ⇒ A
             → Σ ≊ Σ' by A
             → Γ ⊢ Σ' ⇒ e ⇒ A
subsumption (⊢lit regΓ) ≋□ = ⊢sub (⊢lit regΓ) ne-τ gc-i (s-type (s-int (reg-Z regΓ)))
subsumption (⊢var regΓ x∈Γ) ≋□ = ⊢sub (⊢var regΓ x∈Γ) ne-τ gc-var (s-type (s-refl (reg-Z regΓ) (⊢r-𝕣 (∋⦂-⊢r regΓ x∈Γ))))
subsumption (⊢ann ⊢e) ≋□ with t-⊢rᶜ ⊢e
... | ⊢rᶜ-τ regA = ⊢sub (⊢ann ⊢e) ne-τ gc-ann (s-type (s-refl (reg-Z (t-env ⊢e)) (⊢r-𝕣 regA)))
subsumption (⊢app ⊢e) new = ⊢app (subsumption ⊢e (≊S new))
subsumption (⊢lam₂ ⊢e up-c ⊢e₁) (≊S new) = ⊢lam₂ ⊢e {!!} (subsumption ⊢e₁ {!!})
subsumption (⊢sub ⊢e ne gc s) new = ⊢sub ⊢e {!s-subsumtion!} gc (s-subsumtion s new)
subsumption (⊢tabs ⊢e) ≋□ = ⊢sub (⊢tabs ⊢e) ne-τ gc-tlam (s-type (s-refl (reg-Z (t-env (⊢tabs ⊢e))) (⊢r-𝕣 (⊢r-∀ (t-⊢r ⊢e)))))
subsumption (⊢tapp ⊢e st) new = ⊢tapp (subsumption ⊢e (≊⓪ new st)) st

subsumption0 : Γ ⊢ □ ⇒ e ⇒ A
             → Γ ⊢ τ A ⇒ e ⇒ A
subsumption0 ⊢e = subsumption ⊢e ≋□
