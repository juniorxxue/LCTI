module Implicit.Interm.Base where

open import Implicit.Language.All

----------------------------------------------------------------------
--+                           Subtyping                            +--
----------------------------------------------------------------------

infix 3 _⊢_#_⌞_⌝_
data _⊢_#_⌞_⌝_ : Env n m → Counter m → Type m → Polar → Type m → Set where
  s-refl+ :
      (regΔ : SRegular Δ)
    → (cloA : Δ ⊢c A)
    → (grd : Δ ≫ A ⇘ A%)
    → Δ ⊢ `𝕫 # A ⌞ ≤⁺ ⌝ A%
  s-refl- :
      (regΔ : SRegular Δ)
    → (cloA : Δ ⊢c A)
    → (grd : Δ ≫ A ⇘ A%)
    → Δ ⊢ `𝕫 # A% ⌞ ≤⁻ ⌝ A
  s-int :
      (regΔ : SRegular Δ)
    → Δ ⊢ `∞ # Int ⌞ ≤ ⌝ Int
  s-var-∙ :
      (regΔ : SRegular Δ)
    → (inΔ : Δ ∋∙ X)
    → Δ ⊢ `∞ # ‶ X ⌞ ≤ ⌝ ‶ X
  s-arr₁ :
      Δ ⊢ `∞ # C ⌞ ⋆ ≤ ⌝ A
    → Δ ⊢ `∞ # B ⌞ ≤ ⌝ D
    → Δ ⊢ `∞ # A `→ B ⌞ ≤ ⌝ C `→ D
  s-arr₂ :
      Δ ⊢ 𝔼 𝕖 # C ⌞ ≤⁻ ⌝ A
    → Δ ⊢ j # B ⌞ ≤⁺ ⌝ D
    → Δ ⊢ 𝕊₍ 𝕖 ₎ j # A `→ B ⌞ ≤⁺ ⌝ C `→ D
  s-arr-n :
      Δ ⊢ `∞ # C ⌞ ≤⁺ ⌝ A
    → Δ ⊢ `𝕟 i # B ⌞ ≤⁻ ⌝ D
    → Δ ⊢ `𝕟 (suc i) # A `→ B ⌞ ≤⁻ ⌝ C `→ D
  s-∀ :
      Δ ,∙ ⊢ `∞ # A ⌞ ≤ ⌝ B
    → Δ ⊢ `∞ # `∀ A ⌞ ≤ ⌝ `∀ B
  s-∀l :
      Δ ,= B ⊢ (𝕊₍ 𝕖 ₎ j') # A ⌞ ≤⁺ ⌝ C' `→ D'
--    → (fd : find2 A #0 (𝕊₍ w' ₎ j'))
    → (upC : ↑ty0 C ⇘ C')
    → (upD : ↑ty0 D ⇘ D')
    → (upj : ↑tyʲ0 j ⇘ j')
    → Δ ⊢ (𝕊₍ 𝕖 ₎ j) # `∀ A ⌞ ≤⁺ ⌝ C `→ D
  s-tapp :
      Δ ,= B ⊢ j' # A ⌞ ≤⁺ ⌝ C
    → (upj : ↑tyʲ0 j ⇘ j')
    → Δ ⊢ 𝕋₍ B ₎ j # `∀ A ⌞ ≤⁺ ⌝ `∀ C
  -- two atomic rules
  s-svar-l : ∀ {X A}
    → (SRegular Δ)
    → (inΔ : Δ ∋ X := A)
    → Δ ⊢ `∞ # ‶ X ⌞ ≤⁺ ⌝ A
  s-svar-r : ∀ {X A}
    → (SRegular Δ)
    → (inΔ : Δ ∋ X := A)
    → Δ ⊢ `∞ # A ⌞ ≤⁻ ⌝ ‶ X

s-refl-∞ : SRegular Γ
         → Γ ⊢r A
         → Γ ⊢ `∞ # A ⌞ ≤ ⌝ A
s-refl-∞ regΓ ⊢r-int = s-int regΓ
s-refl-∞ regΓ (⊢r-var-∙ inΓ) = s-var-∙ regΓ inΓ
s-refl-∞ regΓ (⊢r-arr regA regA₁) = s-arr₁ (s-refl-∞ regΓ regA) (s-refl-∞ regΓ regA₁)
s-refl-∞ regΓ (⊢r-∀ regA) = s-∀ (s-refl-∞ (reg-S∙ regΓ) regA)

----------------------------------------------------------------------
--+                             Typing                             +--
----------------------------------------------------------------------

infix 3 _⊢_#_⦂_
data _⊢_#_⦂_ : Env n m → Counter m → Term n m → Type m → Set where
  ⊢lit : ∀ {num : ℕ}
    → (regΓ : TRegular Γ)
    → Γ ⊢ `𝕫 # (lit num) ⦂ Int
  ⊢var :
      (regΓ : TRegular Γ)
    → (x∈Γ : Γ ∋ x ⦂ A)
    → Γ ⊢ `𝕫 # ` x ⦂ A
  ⊢ann :
      Γ ⊢ `∞ # e ⦂ A
    → Γ ⊢ `𝕫 # (e ⦂ A) ⦂ A
  ⊢lam₁ :
      Γ , A ⊢ `∞ # e ⦂ B
    → Γ ⊢ `∞ # ƛ e ⦂ A `→ B
  ⊢lam₂ :
      Γ , A ⊢ j # e ⦂ B
    → Γ ⊢ 𝕊₍ 𝕟 0 ₎ j # ƛ e ⦂ A `→ B
  ⊢lam₃ :
      Γ , A ⊢ 𝔼 (𝕟 i) # e ⦂ B
    → Γ ⊢ 𝔼 (𝕟 (suc i)) # ƛ e ⦂ A `→ B
  ⊢app :
      Γ ⊢ 𝕊₍ 𝕖 ₎ j # e₁ ⦂ A `→ B
    → Γ ⊢ 𝔼 𝕖 # e₂ ⦂ A
    → Γ ⊢ j # e₁ · e₂ ⦂ B
  ⊢sub :
      Γ ⊢ `𝕫 # g ⦂ A
    → (B≤A : Γ ⋈ ⊢ j # A ⌞ ≤⁺ ⌝ B)
    → (gc : GenericConsumer g)
    → (j≢Z : NonZ j)
    → Γ ⊢ j # g ⦂ B
  ⊢tabs :
      Γ ,∙ ⊢ `𝕫 # e ⦂ A
    → Γ ⊢ `𝕫 # Λ e ⦂ `∀ A
  ⊢tapp : Γ ⊢ 𝕋₍ A ₎ j # e ⦂ `∀ B
        → (st : ⟦ A ⟧ B ⇘ B*)
        → Γ ⊢ j # e ⓪ A ⦂ B*
