module Implicit.Algo.Constructs.Shift where

-- a module for shifting in new syntax of algorithmic system

open import Implicit.Language.All
open import Implicit.Algo.Constructs.Syntax

infix 3 _↑tmᶜ_⇘_
data _↑tmᶜ_⇘_ : Context n m → Fin (1 + n) → Context (1 + n) m → Set where
  ↑tmᶜ-𝔼 : (Context n m ∋⦂ 𝔼 δ) ↑tmᶜ x ⇘ 𝔼 δ
  ↑tmᶜ-e : (up-e : e ↑tm x ⇘ e')
         → Σ ↑tmᶜ x ⇘ Σ'
         → [ e ]↝ Σ ↑tmᶜ x ⇘ [ e' ]↝ Σ'
  ↑tmᶜ-⓪ : Σ ↑tmᶜ x ⇘ Σ'
         → (A ⓪↝ Σ) ↑tmᶜ x ⇘ A ⓪↝ Σ'

infix 3 ↑tmᶜ0_⇘_
↑tmᶜ0_⇘_ : Context n m → Context (1 + n) m → Set
↑tmᶜ0_⇘_ Σ = _↑tmᶜ_⇘_ Σ #0

infix 3 _↑tyᵖ_⇘_
data _↑tyᵖ_⇘_ : ParType m → Fin (1 + m) → ParType (1 + m) → Set where
  ↑tyᵖ-nil : □ ↑tyᵖ k ⇘ □
  ↑tyᵖ-S : (upA : A ↑ty k ⇘ A')
         → P ↑tyᵖ k ⇘ P'
         → A ◐↝ P ↑tyᵖ k ⇘ A' ◐↝ P'

infix 3 _↑tyᴱ_⇘_
data _↑tyᴱ_⇘_ : EContext m → Fin (1 + m) → EContext (1 + m) → Set where
  ↑tyᴱ-τ : (upA : A ↑ty k ⇘ A')
         → (τ A) ↑tyᴱ k ⇘ (τ A')
  ↑tyᴱ-p : P ↑tyᵖ k ⇘ P'
         → (p P) ↑tyᴱ k ⇘ (p P')

infix 3 _↑tyᶜ_⇘_
data _↑tyᶜ_⇘_ : Context n m → Fin (1 + m) → Context n (1 + m) → Set where
  ↑tyᶜ-𝔼 : δ ↑tyᴱ k ⇘ δ'
         → (Context n m ∋⦂ (𝔼 δ)) ↑tyᶜ k ⇘ (𝔼 δ')
  ↑tyᶜ-e : (up-e : e ↑tyᵉ k ⇘ e')
         → Σ ↑tyᶜ k ⇘ Σ'
         → [ e ]↝ Σ ↑tyᶜ k ⇘ [ e' ]↝ Σ'
  ↑tyᶜ-⓪ : (upA : A ↑ty k ⇘ A')
         → Σ ↑tyᶜ k ⇘ Σ'
         → (A ⓪↝ Σ) ↑tyᶜ k ⇘ A' ⓪↝ Σ'

infix 3 ↑tyᶜ0_⇘_
↑tyᶜ0_⇘_ : Context n m → Context n (1 + m) → Set
↑tyᶜ0_⇘_ Σ = _↑tyᶜ_⇘_ Σ #0
