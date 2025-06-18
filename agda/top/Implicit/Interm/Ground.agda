module Implicit.Interm.Ground where

open import Implicit.Language.All
open import Implicit.Interm.Base


grd-reg-input : Γ ≫ A ⇘ B
              → Γ ⊢r A
              → A ≡ B
grd-reg-input grd-top ⊢r-top = refl
grd-reg-input grd-int ⊢r-int = refl
grd-reg-input (grd-var= x) (⊢r-var-∙ inΓ) = ⊥-elim (∋∙-∋:=-false inΓ x)
grd-reg-input (grd-var∙ x) regA = refl
grd-reg-input (grd-arr grd grd₁) (⊢r-arr regA regA₁) rewrite grd-reg-input grd regA | grd-reg-input grd₁ regA₁ = refl
grd-reg-input (grd-∀ grd) (⊢r-∀ regA) rewrite grd-reg-input grd regA = refl
