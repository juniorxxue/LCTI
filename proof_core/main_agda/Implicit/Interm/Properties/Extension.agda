module Implicit.Interm.Properties.Extension where

open import Implicit.Language.All
open import Implicit.Interm.Base
open import Implicit.Interm.Properties.Regularity

s-⊆-prv : Γ ⊢ j # A ⌞ ≤ ⌝ B
        → Γ ⊆ Δ
        → Δ ⊢ j # A ⌞ ≤ ⌝ B
s-⊆-prv (s-refl regΔ cloA grd) ext = s-refl (⊆-sregular' ext) (⊆-⊢c cloA ext) (⊆-⊢c-≫' ext cloA grd)
s-⊆-prv (s-int regΔ) ext = s-int (⊆-sregular' ext)
s-⊆-prv (s-var-∙ regΔ inΔ) ext = s-var-∙ (⊆-sregular' ext) (⊆-∋∙ inΔ ext)
s-⊆-prv (s-arr₁ s s₁) ext = s-arr₁ (s-⊆-prv s ext) (s-⊆-prv s₁ ext)
s-⊆-prv (s-arr₂ s s₁) ext = s-arr₂ (s-⊆-prv s ext) (s-⊆-prv s₁ ext)
s-⊆-prv (s-arr₃ cloA grd s) ext = s-arr₃ (⊆-⊢c cloA ext) (⊆-⊢c-≫' ext cloA grd) (s-⊆-prv s ext)
s-⊆-prv (s-∀ s) ext = s-∀ (s-⊆-prv s (uvar ext))
s-⊆-prv (s-∀l s ic fd upC upD upj) ext with s-sregular s
... | reg-S= r regA = s-∀l (s-⊆-prv s (svar ext regA)) ic fd upC upD upj
s-⊆-prv (s-∀l-no-appear s ic fd upC upD upj) ext with s-sregular s
... | reg-S^ r = s-∀l-no-appear (s-⊆-prv s (evar ext)) ic fd upC upD upj
s-⊆-prv (s-svar-l x inΔ) ext = s-svar-l (⊆-∋:= x ext) (s-⊆-prv inΔ ext)
s-⊆-prv (s-svar-r x inΔ) ext = s-svar-r (⊆-sregular' ext) (⊆-∋:= inΔ ext)
s-⊆-prv (s-tapp s upj) ext with s-sregular s
... | reg-S= r regA = s-tapp (s-⊆-prv s (svar ext regA)) upj


⊆t-⊢c-≫ : Γ ≫ A ⇘ B
        → Γ ⊆t Δ
        → Γ ⊢c A
        → Δ ≫ A ⇘ B
⊆t-⊢c-≫ grd-int ext ⊢c-int = grd-int
⊆t-⊢c-≫ (grd-var= x) ext (⊢c-var-∙ inΔ) = ⊥-elim (∋∙-∋:=-false inΔ x)
⊆t-⊢c-≫ (grd-var= x) ext (⊢c-var-= inΔ) = grd-var= (⊆t-∋:= x ext)
⊆t-⊢c-≫ (grd-var∙ x) ext (⊢c-var-∙ inΔ) = grd-var∙ (⊆t-∋∙ x ext)
⊆t-⊢c-≫ (grd-var∙ x) ext (⊢c-var-= inΔ) = ⊥-elim (∋∙-∋=-false x inΔ)
⊆t-⊢c-≫ (grd-arr grd grd₁) ext (⊢c-arr cloA cloA₁) = grd-arr (⊆t-⊢c-≫ grd ext cloA) (⊆t-⊢c-≫ grd₁ ext cloA₁)
⊆t-⊢c-≫ (grd-∀ grd) ext (⊢c-∀ cloA) = grd-∀ (⊆t-⊢c-≫ grd (uvar ext) cloA)

s-⊆-prv-gen : Γ ⊢ j # A ⌞ ≤ ⌝ B
         → Γ ⊆t Δ
         → Δ ⊢ j # A ⌞ ≤ ⌝ B
s-⊆-prv-gen (s-refl regΔ cloA grd) ext = s-refl (⊆t-sregular regΔ ext) (⊆t-⊢c cloA ext) (⊆t-⊢c-≫ grd ext cloA)
s-⊆-prv-gen (s-int regΔ) ext = s-int (⊆t-sregular regΔ ext)
s-⊆-prv-gen (s-var-∙ regΔ inΔ) ext = s-var-∙ (⊆t-sregular regΔ ext) (⊆t-∋∙ inΔ ext)
s-⊆-prv-gen (s-arr₁ s s₁) ext = s-arr₁ (s-⊆-prv-gen s ext) (s-⊆-prv-gen s₁ ext)
s-⊆-prv-gen (s-arr₂ s s₁) ext = s-arr₂ (s-⊆-prv-gen s ext) (s-⊆-prv-gen s₁ ext)
s-⊆-prv-gen (s-arr₃ cloA grd s) ext = s-arr₃ (⊆t-⊢c cloA ext) (⊆t-⊢c-≫ grd ext cloA) (s-⊆-prv-gen s ext)
s-⊆-prv-gen (s-∀ s) ext = s-∀ (s-⊆-prv-gen s (uvar ext))
s-⊆-prv-gen (s-∀l s ic fd upC upD upj) ext with s-sregular s
... | reg-S= r regA = s-∀l (s-⊆-prv-gen s (svar ext regA)) ic fd upC upD upj
s-⊆-prv-gen (s-∀l-no-appear s ic fd upC upD upj) ext with s-sregular s
... | reg-S^ r = s-∀l-no-appear (s-⊆-prv-gen s (evar ext)) ic fd upC upD upj
s-⊆-prv-gen (s-svar-l x inΔ) ext = s-svar-l (⊆t-∋:= x ext) (s-⊆-prv-gen inΔ ext)
s-⊆-prv-gen (s-svar-r x inΔ) ext = s-svar-r (⊆t-sregular x ext) (⊆t-∋:= inΔ ext)
s-⊆-prv-gen (s-tapp s st) ext with s-sregular s
... | reg-S= r regA = s-tapp (s-⊆-prv-gen s (svar ext regA)) st

t-⊆-prv-gen : Γ ⊢ j # e ⦂ A
        → Γ ⊆t Δ
        → Δ ⊢ j # e ⦂ A
t-⊆-prv-gen (⊢lit cloΓ) ext = ⊢lit (⊆t-tregular cloΓ ext)
t-⊆-prv-gen (⊢var cloΓ x∈Γ) ext = ⊢var (⊆t-tregular cloΓ ext) (⊆t-∋⦂ x∈Γ ext)
t-⊆-prv-gen (⊢ann ⊢e) ext = ⊢ann (t-⊆-prv-gen ⊢e ext)
t-⊆-prv-gen (⊢lam₁ ⊢e) ext with t-tregular ⊢e
... | reg-S, r regA = ⊢lam₁ (t-⊆-prv-gen ⊢e (tvar ext regA))
t-⊆-prv-gen (⊢lam₂ ⊢e) ext with t-tregular ⊢e
... | reg-S, r regA = ⊢lam₂ (t-⊆-prv-gen ⊢e (tvar ext regA))
t-⊆-prv-gen (⊢app₁ ⊢e ⊢e₁) ext = ⊢app₁ (t-⊆-prv-gen ⊢e ext) (t-⊆-prv-gen ⊢e₁ ext)
t-⊆-prv-gen (⊢app₂ ⊢e ⊢e₁) ext = ⊢app₂ (t-⊆-prv-gen ⊢e ext) (t-⊆-prv-gen ⊢e₁ ext)
t-⊆-prv-gen (⊢sub ⊢e B≤A x j≢Z) ext = ⊢sub (t-⊆-prv-gen ⊢e ext) (s-⊆-prv-gen B≤A (mark ext)) x j≢Z
t-⊆-prv-gen (⊢tabs ⊢e) ext = ⊢tabs (t-⊆-prv-gen ⊢e (uvar ext))
t-⊆-prv-gen (⊢tabs-∞ ⊢e) ext = ⊢tabs-∞ (t-⊆-prv-gen ⊢e (uvar ext))
t-⊆-prv-gen (⊢tapp ⊢e st) ext = ⊢tapp (t-⊆-prv-gen ⊢e ext) st

----------------------------------------------------------------------
--+                          corollaries                           +--
----------------------------------------------------------------------


t-⊆-prv : 𝕣 Γ ⊢ j # e ⦂ A
         → Γ ⊆ Δ
         → 𝕣 Δ ⊢ j # e ⦂ A
t-⊆-prv ⊢e ext = t-⊆-prv-gen ⊢e (⊆-⊆t-𝕣 ext)
