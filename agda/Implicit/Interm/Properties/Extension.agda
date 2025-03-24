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
s-⊆-prv (s-∀l s ic fd upC upD) ext with s-sregular s
... | reg-S= r regA = s-∀l (s-⊆-prv s (svar ext regA)) ic fd upC upD
s-⊆-prv (s-svar-l x inΔ) ext = s-svar-l (⊆-sregular' ext) (⊆-∋:= inΔ ext)
s-⊆-prv (s-svar-r x inΔ) ext = s-svar-r (⊆-sregular' ext) (⊆-∋:= inΔ ext)

infix 3 _⊆t_
data _⊆t_ : Env n m → Env n m → Set where
  empty : ∅ ⊆t ∅
  tvar : Γ ⊆t Δ
       → (regA : Γ ⊢r A)
       → Γ , A ⊆t Δ , A
  uvar :
      Γ ⊆t Δ
    → Γ ,∙ ⊆t Δ ,∙
  evar :
      Γ ⊆t Δ
    → Γ ,^ ⊆t Δ ,^
  evar-sol :
      Γ ⊆t Δ
    → (regA : Δ ⊢r A)
    → Γ ,^ ⊆t Δ ,= A
  svar :
      Γ ⊆t Δ
    → (regA : Γ ⊢r A)
    → Γ ,= A ⊆t Δ ,= A
  mark : Γ ⊆t Δ
       → Γ ⋈ ⊆t Δ ⋈

⊆t-∋⦂ : Γ ∋ x ⦂ A
      → Γ ⊆t Δ
      → Δ ∋ x ⦂ A
⊆t-∋⦂ Z (tvar ext regA) = Z
⊆t-∋⦂ (S, inΓ) (tvar ext regA) = S, (⊆t-∋⦂ inΓ ext)
⊆t-∋⦂ (S∙ inΓ up) (uvar ext) = S∙ (⊆t-∋⦂ inΓ ext) up
⊆t-∋⦂ (S^ inΓ up) (evar ext) = S^ (⊆t-∋⦂ inΓ ext) up
⊆t-∋⦂ (S^ inΓ up) (evar-sol ext regA) = S= (⊆t-∋⦂ inΓ ext) up
⊆t-∋⦂ (S= inΓ up) (svar ext regA) = S= (⊆t-∋⦂ inΓ ext) up

⊆t-∋∙ : Γ ∋∙ X
      → Γ ⊆t Δ
      → Δ ∋∙ X
⊆t-∋∙ Z (uvar ext) = Z
⊆t-∋∙ (S, inΓ) (tvar ext regA) = S, (⊆t-∋∙ inΓ ext)
⊆t-∋∙ (S∙ inΓ) (uvar ext) = S∙ (⊆t-∋∙ inΓ ext)
⊆t-∋∙ (S= inΓ) (svar ext regA) = S= (⊆t-∋∙ inΓ ext)
⊆t-∋∙ (S^ inΓ) (evar ext) = S^ (⊆t-∋∙ inΓ ext)
⊆t-∋∙ (S^ inΓ) (evar-sol ext regA) = S= (⊆t-∋∙ inΓ ext)
⊆t-∋∙ (S⋈ inΓ) (mark ext) = S⋈ (⊆t-∋∙ inΓ ext)

⊆t-∋:= : Γ ∋ k := A
       → Γ ⊆t Δ
       → Δ ∋ k := A
⊆t-∋:= (Z up) (svar ext regA) = Z up
⊆t-∋:= (S∙ inΓ up) (uvar ext) = S∙ (⊆t-∋:= inΓ ext) up
⊆t-∋:= (S^ inΓ up) (evar ext) = S^ (⊆t-∋:= inΓ ext) up
⊆t-∋:= (S^ inΓ up) (evar-sol ext regA) = S= (⊆t-∋:= inΓ ext) up
⊆t-∋:= (S= inΓ up) (svar ext regA) = S= (⊆t-∋:= inΓ ext) up
⊆t-∋:= (S, inΓ) (tvar ext regA) = S, (⊆t-∋:= inΓ ext)

⊆t-∋= : Γ ∋= k
       → Γ ⊆t Δ
       → Δ ∋= k
⊆t-∋= Z (svar ext regA) = Z
⊆t-∋= (S∙ inΓ) (uvar ext) = S∙ (⊆t-∋= inΓ ext)
⊆t-∋= (S^ inΓ) (evar ext) = S^ (⊆t-∋= inΓ ext)
⊆t-∋= (S^ inΓ) (evar-sol ext regA) = S= (⊆t-∋= inΓ ext)
⊆t-∋= (S= inΓ) (svar ext regA) = S= (⊆t-∋= inΓ ext)
⊆t-∋= (S, inΓ) (tvar ext regA) = S, (⊆t-∋= inΓ ext)


⊆t-⊢r : Γ ⊢r A
      → Γ ⊆t Δ
      → Δ ⊢r A
⊆t-⊢r ⊢r-int ext = ⊢r-int
⊆t-⊢r (⊢r-var-∙ inΓ) ext = ⊢r-var-∙ (⊆t-∋∙ inΓ ext)
⊆t-⊢r (⊢r-arr regA regA₁) ext = ⊢r-arr (⊆t-⊢r regA ext) (⊆t-⊢r regA₁ ext)
⊆t-⊢r (⊢r-∀ regA) ext = ⊢r-∀ (⊆t-⊢r regA (uvar ext))

⊆t-⊢c : Γ ⊢c A
      → Γ ⊆t Δ
      → Δ ⊢c A
⊆t-⊢c ⊢c-int ext = ⊢c-int
⊆t-⊢c (⊢c-var-∙ inΔ) ext = ⊢c-var-∙ (⊆t-∋∙ inΔ ext)
⊆t-⊢c (⊢c-var-= inΔ) ext = ⊢c-var-= (⊆t-∋= inΔ ext)
⊆t-⊢c (⊢c-arr cloA cloA₁) ext = ⊢c-arr (⊆t-⊢c cloA ext) (⊆t-⊢c cloA₁ ext)
⊆t-⊢c (⊢c-∀ cloA) ext = ⊢c-∀ (⊆t-⊢c cloA (uvar ext))

⊆t-tregular : TRegular Γ
            → Γ ⊆t Δ
            → TRegular Δ
⊆t-tregular reg-Z empty = reg-Z
⊆t-tregular (reg-S, regΓ regA) (tvar ext regA₁) = reg-S, (⊆t-tregular regΓ ext) (⊆t-⊢r regA ext)
⊆t-tregular (reg-S∙ regΓ) (uvar ext) = reg-S∙ (⊆t-tregular regΓ ext)
⊆t-tregular (reg-S^ regΓ) (evar ext) = reg-S^ (⊆t-tregular regΓ ext)
⊆t-tregular (reg-S^ regΓ) (evar-sol ext regA) = reg-S= (⊆t-tregular regΓ ext) regA
⊆t-tregular (reg-S= regΓ regA) (svar ext regA₁) = reg-S= (⊆t-tregular regΓ ext) (⊆t-⊢r regA ext)

⊆t-sregular : SRegular Γ
            → Γ ⊆t Δ
            → SRegular Δ
⊆t-sregular (reg-Z regΓ) (mark ext) = reg-Z (⊆t-tregular regΓ ext)
⊆t-sregular (reg-S∙ regΓ) (uvar ext) = reg-S∙ (⊆t-sregular regΓ ext)
⊆t-sregular (reg-S^ regΓ) (evar ext) = reg-S^ (⊆t-sregular regΓ ext)
⊆t-sregular (reg-S^ regΓ) (evar-sol ext regA) = reg-S= (⊆t-sregular regΓ ext) regA
⊆t-sregular (reg-S= regΓ regA) (svar ext regA₁) = reg-S= (⊆t-sregular regΓ ext) (⊆t-⊢r regA ext)

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
s-⊆-prv-gen (s-∀l s ic fd upC upD) ext with s-sregular s
... | reg-S= r regA = s-∀l (s-⊆-prv-gen s (svar ext regA)) ic fd upC upD
s-⊆-prv-gen (s-svar-l x inΔ) ext = s-svar-l (⊆t-sregular x ext) (⊆t-∋:= inΔ ext)
s-⊆-prv-gen (s-svar-r x inΔ) ext = s-svar-r (⊆t-sregular x ext) (⊆t-∋:= inΔ ext)

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

----------------------------------------------------------------------
--+                          corollaries                           +--
----------------------------------------------------------------------

⊆-refl-tregular : TRegular Γ
                → Γ ⊆t Γ
⊆-refl-tregular reg-Z = empty
⊆-refl-tregular (reg-S, treg regA) = tvar (⊆-refl-tregular treg) regA
⊆-refl-tregular (reg-S∙ treg) = uvar (⊆-refl-tregular treg)
⊆-refl-tregular (reg-S^ treg) = evar (⊆-refl-tregular treg)
⊆-refl-tregular (reg-S= treg regA) = svar (⊆-refl-tregular treg) regA

⊆-refl-sregular : SRegular Γ
                → Γ ⊆t Γ
⊆-refl-sregular (reg-Z regΓ) = mark (⊆-refl-tregular regΓ)
⊆-refl-sregular (reg-S∙ sreg) = uvar (⊆-refl-sregular sreg)
⊆-refl-sregular (reg-S^ sreg) = evar (⊆-refl-sregular sreg)
⊆-refl-sregular (reg-S= sreg regA) = svar (⊆-refl-sregular sreg) regA


⊆-⊆t : Γ ⊆ Δ
     → Γ ⊆t Δ
⊆-⊆t (uvar ext) = uvar (⊆-⊆t ext)
⊆-⊆t (evar ext) = evar (⊆-⊆t ext)
⊆-⊆t (evar-sol ext regA) = evar-sol (⊆-⊆t ext) regA
⊆-⊆t (svar ext regA) = svar (⊆-⊆t ext) regA
⊆-⊆t (mark regΓ) = mark (⊆-refl-tregular regΓ)

⊆-⊆t-𝕣 : Γ ⊆ Δ
      → 𝕣 Γ ⊆t 𝕣 Δ
⊆-⊆t-𝕣 (uvar ext) = uvar (⊆-⊆t-𝕣 ext)
⊆-⊆t-𝕣 (evar ext) = evar (⊆-⊆t-𝕣 ext)
⊆-⊆t-𝕣 (evar-sol ext regA) = evar-sol (⊆-⊆t-𝕣 ext) (⊢r-𝕣' regA)
⊆-⊆t-𝕣 (svar ext regA) = svar (⊆-⊆t-𝕣 ext) (⊢r-𝕣' regA)
⊆-⊆t-𝕣 (mark regΓ) = ⊆-refl-tregular regΓ

t-⊆-prv : 𝕣 Γ ⊢ j # e ⦂ A
         → Γ ⊆ Δ
         → 𝕣 Δ ⊢ j # e ⦂ A
t-⊆-prv ⊢e ext = t-⊆-prv-gen ⊢e (⊆-⊆t-𝕣 ext)
