module Implicit.Algo.Properties.PShift where

open import Implicit.Language.All
open import Implicit.Algo.Base

postulate
  ↑tmᶜ-total : ∀ (Σ : Context n m) (k)
    → ∃ λ Σ'
    → Σ ↑tmᶜ k ⇘ Σ'

postulate
  ↑tmᶜ0-total : ∀ (Σ : Context n m)
    → ∃ λ Σ'
    → ↑tmᶜ0 Σ ⇘ Σ'

postulate
  ↑tmᶜ-unique : Σ ↑tmᶜ k ⇘ Σ₁
              → Σ ↑tmᶜ k ⇘ Σ₂
              → Σ₁ ≡ Σ₂

postulate
  ↑tyᶜ-total : ∀ (Σ : Context n m) (k)
    → ∃ λ Σ'
    → Σ ↑tyᶜ k ⇘ Σ'

postulate
  ↑tyᶜ0-total : ∀ (Σ : Context n m)
    → ∃ λ Σ'
    → ↑tyᶜ0 Σ ⇘ Σ'

postulate
  ↑tm-↑tyᵉ-comm' : e ↑tm k₁ ⇘ e₁
                  → e ↑tyᵉ k₂ ⇘ e'
                  → e' ↑tm k₁ ⇘ e₂
                  → e₁ ↑tyᵉ k₂ ⇘ e₂

postulate
  ↑tmᶜ-↑tyᶜ-comm' : Σ ↑tmᶜ k₁ ⇘ Σ₁
                  → Σ ↑tyᶜ k₂ ⇘ Σ'
                  → Σ' ↑tmᶜ k₁ ⇘ Σ₂
                  → Σ₁ ↑tyᶜ k₂ ⇘ Σ₂

postulate
  ↑tyᶜ-comm0' : ∀ {Σ : Context n m} {Σₖ Σₖ₊₁ Σ₀ k}
              → Σ ↑tyᶜ k ⇘ Σₖ
              → ↑tyᶜ0 Σₖ ⇘ Σₖ₊₁
              ---------------------
              → ↑tyᶜ0 Σ ⇘ Σ₀
              → Σ₀ ↑tyᶜ #S k ⇘ Σₖ₊₁
postulate
  ↑tm-↑tyᵉ-comm : e ↑tm k₁ ⇘ e₁
               → e₁ ↑tyᵉ k₂ ⇘ e₂
               → e ↑tyᵉ k₂ ⇘ e'
               → e' ↑tm k₁ ⇘ e₂

postulate
  ↑tmᶜ-↑tyᶜ-comm : Σ ↑tmᶜ k₁ ⇘ Σ₁
                 → Σ₁ ↑tyᶜ k₂ ⇘ Σ₂
                 → Σ ↑tyᶜ k₂ ⇘ Σ'
                 → Σ' ↑tmᶜ k₁ ⇘ Σ₂

postulate
  ↑tmᶜ-comm' : k₁ #≤ k₂
           → Σ ↑tmᶜ k₂ ⇘ Σ₁
           → Σ₁ ↑tmᶜ (inject₁ k₁) ⇘ Σ₂
           ----------------
           → Σ ↑tmᶜ k₁ ⇘ Σ'
           → Σ' ↑tmᶜ #S k₂ ⇘ Σ₂

postulate
  nonempty-↑tmᶜ' : NonEmpty Σ'
                → Σ ↑tmᶜ k ⇘ Σ'
                → NonEmpty Σ

postulate
  nonempty-↑tmᶜ : NonEmpty Σ
                → Σ ↑tmᶜ k ⇘ Σ'
                → NonEmpty Σ'

postulate
  nonempty-↑tyᶜ : NonEmpty Σ'
                → Σ ↑tyᶜ k ⇘ Σ'
                → NonEmpty Σ

postulate
  nonempty-↑tyᶜ' : NonEmpty Σ
                 → Σ ↑tyᶜ k ⇘ Σ'
                 → NonEmpty Σ'

postulate
  gc-↑tyᵉ : GenericConsumer e
          → e ↑tyᵉ k ⇘ e'
          → GenericConsumer e'
