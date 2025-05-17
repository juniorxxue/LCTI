module Implicit.Interm.Properties.PRegularity where

open import Implicit.Language.All hiding (_⊢rʲ_)
open import Implicit.Interm.Base

postulate
  s-sregular : Γ ⊢ j # A ⌞ ≤ ⌝ B
             → SRegular Γ

postulate
  t-tregular : Γ ⊢ j # e ⦂ A
             → TRegular Γ

infix 3 _⊢rʲ_

data _⊢rʲ_ : Env n m → Counter m → Set where
  j-Z : Γ ⊢rʲ `𝕫
  j-∞ : Γ ⊢rʲ `∞
  j-𝕊 : Γ ⊢rʲ j
      → Γ ⊢rʲ (𝕊₍ 𝕖 ₎ j)
  j-𝕋 : Γ ⊢rʲ j
      → Γ ⊢r A
      → Γ ⊢rʲ 𝕋₍ A ₎ j


postulate
  ⊢rʲ-strengthen=0 : Γ ,= T ⊢rʲ j'
                   → ↑tyʲ0 j ⇘ j'
                   → Γ ⊢rʲ j

postulate
  ⊢rʲ-strengthen,0 : Γ , T ⊢rʲ j
                   → Γ ⊢rʲ j

postulate
  s-⊢rʲ : Γ ⊢ j # A ⌞ ≤ ⌝ B
        → Γ ⊢rʲ j

postulate
  ⊢r-⋈ : Γ ⊢rʲ j
       → 𝕣 Γ ⊢rʲ j

postulate
  t-⊢rʲ : Γ ⊢ j # e ⦂ A
        → Γ ⊢rʲ j
