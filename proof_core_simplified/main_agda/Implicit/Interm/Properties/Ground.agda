module Implicit.Interm.Properties.Ground where

open import Implicit.Language.All
open import Implicit.Interm.Base
open import Implicit.Interm.Properties.Regularity

s+-≫ : Γ ⊢ `□ # A ⌞ ≤⁺ ⌝ B
     → Γ ≫ A ⇘ B

s--≫ : Γ ⊢ `□ # A ⌞ ≤⁻ ⌝ B
     → Γ ≫ B ⇘ A

s+-≫ (s-int cloΓ) = grd-int
s+-≫ (s-var-∙ cloΓ inΓ) = grd-var∙ inΓ
s+-≫ (s-arr₁ s s₁) = grd-arr (s--≫ s) (s+-≫ s₁)
s+-≫ (s-∀ s) = grd-∀ (s+-≫ s)
s+-≫ (s-svar-l inΓ s)
  with ih ← s+-≫ s
  with regC ← ∋:=-⊢r (s-sregular s) inΓ
  with refl ← ⊢r-≫-eq' regC ih
  = grd-var= inΓ

s--≫ (s-int cloΓ) = grd-int
s--≫ (s-var-∙ cloΓ inΓ) = grd-var∙ inΓ
s--≫ (s-arr₁ s s₁) = grd-arr (s+-≫ s) (s--≫ s₁)
s--≫ (s-∀ s) = grd-∀ (s--≫ s)
s--≫ (s-svar-r cloA inΓ) = grd-var= inΓ

grd-reg-input : Γ ≫ A ⇘ B
              → Γ ⊢r A
              → A ≡ B
grd-reg-input grd-int ⊢r-int = refl
grd-reg-input (grd-var= x) (⊢r-var-∙ inΓ) = ⊥-elim (∋∙-∋:=-false inΓ x)
grd-reg-input (grd-var∙ x) regA = refl
grd-reg-input (grd-arr grd grd₁) (⊢r-arr regA regA₁) rewrite grd-reg-input grd regA | grd-reg-input grd₁ regA₁ = refl
grd-reg-input (grd-∀ grd) (⊢r-∀ regA) rewrite grd-reg-input grd regA = refl
