module Implicit.Algo.Constructs.Shift where

-- a module for shifting in new syntax of algorithmic system

open import Implicit.Language.All
open import Implicit.Algo.Constructs.Syntax

infix 3 _↑tmᶜ_⇘_
data _↑tmᶜ_⇘_ : Context n m → Fin (1 + n) → Context (1 + n) m → Set where
  ↑tmᶜ-□ : (Context n m ∋⦂ □) ↑tmᶜ x ⇘ □
  ↑tmᶜ-τ : (Context n m ∋⦂ τ A) ↑tmᶜ x ⇘ (τ A)
  ↑tmᶜ-e : (up-e : e ↑tm x ⇘ e')
         → Σ ↑tmᶜ x ⇘ Σ'
         → [ e ]↝ Σ ↑tmᶜ x ⇘ [ e' ]↝ Σ'
  ↑tmᶜ-⓪ : Σ ↑tmᶜ x ⇘ Σ'
         → (A ⓪↝ Σ) ↑tmᶜ x ⇘ A ⓪↝ Σ'
  ↑tmᶜ-◐ : Σ ↑tmᶜ x ⇘ Σ'
         → (A ◐↝ Σ) ↑tmᶜ x ⇘ A ◐↝ Σ'

infix 3 ↑tmᶜ0_⇘_
↑tmᶜ0_⇘_ : Context n m → Context (1 + n) m → Set
↑tmᶜ0_⇘_ Σ = _↑tmᶜ_⇘_ Σ #0

infix 3 _↑tyᶜ_⇘_
data _↑tyᶜ_⇘_ : Context n m → Fin (1 + m) → Context n (1 + m) → Set where
  ↑tyᶜ-□ : (Context n m ∋⦂ □) ↑tyᶜ k ⇘ □
  ↑tyᶜ-τ : (up-t : A ↑ty k ⇘ A')
         → (Context n m ∋⦂ τ A) ↑tyᶜ k ⇘ (τ A')
  ↑tyᶜ-e : (up-e : e ↑tyᵉ k ⇘ e')
         → Σ ↑tyᶜ k ⇘ Σ'
         → [ e ]↝ Σ ↑tyᶜ k ⇘ [ e' ]↝ Σ'
  ↑tyᶜ-⓪ : (upA : A ↑ty k ⇘ A')
         → Σ ↑tyᶜ k ⇘ Σ'
         → (A ⓪↝ Σ) ↑tyᶜ k ⇘ A' ⓪↝ Σ'
  ↑tyᶜ-◐ : (upA : A ↑ty k ⇘ A')
         → Σ ↑tyᶜ k ⇘ Σ'
         → (A ◐↝ Σ) ↑tyᶜ k ⇘ A' ◐↝ Σ'

infix 3 ↑tyᶜ0_⇘_
↑tyᶜ0_⇘_ : Context n m → Context n (1 + m) → Set
↑tyᶜ0_⇘_ Σ = _↑tyᶜ_⇘_ Σ #0
