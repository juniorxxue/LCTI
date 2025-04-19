module Implicit.Algo.Properties.PTrans where

open import Implicit.Language.All
open import Implicit.Algo.Base
open import Implicit.Algo.Properties.Id
open import Implicit.Algo.Properties.Shift
open import Implicit.Algo.Properties.Extension
open import Implicit.Algo.Properties.Weaken
open import Implicit.Algo.Properties.Regularity
open import Implicit.Algo.Properties.Polarity


postulate
  ≊-↑ty0 : Σ₁ ≊ Σ₂
         → ↑tyᶜ0 Σ₁ ⇘ Σ₁'
         → ↑tyᶜ0 Σ₂ ⇘ Σ₂'
         → Σ₁' ≊ Σ₂'

postulate
  ss-grd+ : SRegular Γ
         → Γ ⊢c A
           → Γ ≫ A ⇘ B
           → Γ ⊢ A ⌞ ≤⁺ ⌝ B ⊣ Γ

postulate
  ss-grd- : SRegular Γ
         → Γ ⊢c A
           → Γ ≫ A ⇘ B
           → Γ ⊢ B ⌞ ≤⁻ ⌝ A ⊣ Γ

postulate
  ss-⊢r-eq+ : Γ ⊢ A ⌞ ≤⁺ ⌝ B ⊣ Γ
            → Γ ⊢r A
            → A ≡ B

postulate
  ss-⊢r-eq- : Γ ⊢ A ⌞ ≤⁻ ⌝ B ⊣ Γ
            → Γ ⊢r B
             → A ≡ B

postulate
  s-trans : Γ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B
          → Δ ⊢ B ≤⁺ Σ' ⊣ Δ ↪ C
          → Σ ≊ Σ'
          → Γ ⊢ A ≤⁺ Σ' ⊣ Δ ↪ C

