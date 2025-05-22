module Implicit.Algo.Properties.PRegularity where

open import Implicit.Language.All
open import Implicit.Algo.Base
open import Implicit.Algo.Properties.Id
open import Implicit.Algo.Properties.Extension
open import Implicit.Algo.Properties.Polarity

----------------------------------------------------------------------
--+                          environments                          +--
----------------------------------------------------------------------

postulate
  t-env : Γ ⊢ Σ ⇒ e ⇒ A
        → TRegular Γ

postulate
  inst-env-in : [ A / X ] Γ ⟹ Δ
              → SRegular Γ

postulate
  ss-env-in : Γ ⊢ A ⌞ ≤ ⌝ B ⊣ Δ
            → SRegular Γ

postulate
  ss-env-out : Γ ⊢ A ⌞ ≤ ⌝ B ⊣ Δ
             → SRegular Δ

postulate
  s-env-in : Γ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B
           → SRegular Γ

postulate
  s-env-out : Γ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B
            → SRegular Δ

postulate
  inst-env-out : [ A / X ] Γ ⟹ Δ
               → SRegular Δ

infix 3 _⊢rᶜ_

data _⊢rᶜ_ : Env n m → Context n m → Set where
  ⊢rᶜ-empty : Γ ⊢rᶜ `□
  ⊢rᶜ-τ : (regA : Γ ⊢r A)
        → Γ ⊢rᶜ (`τ A)
  ⊢rᶜ-term : Γ ⊢rᶜ Σ
           → Γ ⊢rᶜ [ e ]↝ Σ
  ⊢rᶜ-tapp : (regA : Γ ⊢r A)
           → Γ ⊢rᶜ Σ
           → Γ ⊢rᶜ A ⓪↝ Σ

postulate
  ⊆-⊢rᶜ' : Δ ⊢rᶜ Σ
         → Γ ⊆ Δ
         → Γ ⊢rᶜ Σ

postulate
  ⊢rᶜ-strengthen^0 : Γ ,^ ⊢rᶜ Σ'
                   → ↑tyᶜ0 Σ ⇘ Σ'
                   → Γ ⊢rᶜ Σ

postulate
  ⊢rᶜ-strengthen=0 : Γ ,= T ⊢rᶜ Σ'
                   → ↑tyᶜ0 Σ ⇘ Σ'
                   → Γ ⊢rᶜ Σ

postulate
  ⊢rᶜ-strengthen,0 : Γ , A ⊢rᶜ Σ'
                   → ↑tmᶜ0 Σ ⇘ Σ'
                   → Γ ⊢rᶜ Σ

postulate
  ⊢rᶜ-⋈ : Γ ⋈ ⊢rᶜ Σ
        → Γ ⊢rᶜ Σ

postulate
  s-⊢rᶜ : Γ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B
        → Γ ⊢rᶜ Σ

postulate
  t-⊢rᶜ : Γ ⊢ Σ ⇒ e ⇒ A
        → Γ ⊢rᶜ Σ

postulate
  s-⊢r : Γ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B
       → Γ ⊢r B

postulate
  t-⊢r : Γ ⊢ Σ ⇒ e ⇒ A
       → Γ ⊢r A
