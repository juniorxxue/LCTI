module Implicit.Interm.Base where

open import Implicit.Language.All

----------------------------------------------------------------------
--+                           Subtyping                            +--
----------------------------------------------------------------------

infix 3 _⊢_#_⌞_⌝_
data _⊢_#_⌞_⌝_ : Env n m → Mask → Type m → Polar → Type m → Set where
  s-refl :
      (regΔ : SRegular Δ)
    → (cloA : Δ ⊢c A)
    → (grd : Δ ≫ A ⇘ A%)
    → Δ ⊢ `■ # A ⌞ ≤⁺ ⌝ A%
  s-int :
      (regΔ : SRegular Δ)
    → Δ ⊢ `□ # Int ⌞ ≤ ⌝ Int
  s-var-∙ :
      (regΔ : SRegular Δ)
    → (inΔ : Δ ∋∙ X)
    → Δ ⊢ `□ # ‶ X ⌞ ≤ ⌝ ‶ X
  s-arr₁ :
      Δ ⊢ `□ # C ⌞ ⋆ ≤ ⌝ A
    → Δ ⊢ `□ # B ⌞ ≤ ⌝ D
    → Δ ⊢ `□ # A `→ B ⌞ ≤ ⌝ C `→ D
  s-arr₂ :
      Δ ⊢ `□ # C ⌞ ≤⁻ ⌝ A
    → Δ ⊢ j # B ⌞ ≤⁺ ⌝ D
    → Δ ⊢ □ · j # A `→ B ⌞ ≤⁺ ⌝ C `→ D
  s-arr₃ :
      (cloA : Δ ⊢c A)
    → (grd : Δ ≫ A ⇘ A%)
    → Δ ⊢ j # B ⌞ ≤⁺ ⌝ D
    → Δ ⊢ ■ · j # A `→ B ⌞ ≤⁺ ⌝ A% `→ D
  s-∀ :
      Δ ,∙ ⊢ `□ # A ⌞ ≤ ⌝ B
    → Δ ⊢ `□ # `∀ A ⌞ ≤ ⌝ `∀ B
  s-∀l :
      Δ ,= B ⊢ (i · j) # A ⌞ ≤⁺ ⌝ C' `→ D'
    → (fd : find A #0 (i · j))
    → (upC : ↑ty0 C ⇘ C')
    → (upD : ↑ty0 D ⇘ D')
    → Δ ⊢ (i · j) # `∀ A ⌞ ≤⁺ ⌝ C `→ D
  s-∀l-no-appear :
      Δ ,^ ⊢ (i · j) # A ⌞ ≤⁺ ⌝ C' `→ D'
    → (fd : #0 ¬ε A)
    → (upC : ↑ty0 C ⇘ C')
    → (upD : ↑ty0 D ⇘ D')
    → Δ ⊢ (i · j) # `∀ A ⌞ ≤⁺ ⌝ C `→ D

  -- two atomic rules
  s-svar-l :
      Δ ∋ X := B
    → Δ ⊢ j # B ⌞ ≤⁺ ⌝ A
    → Δ ⊢ j # ‶ X ⌞ ≤⁺ ⌝ A
  s-svar-r : ∀ {X A}
    → (SRegular Δ)
    → (inΔ : Δ ∋ X := A)
    → Δ ⊢ `□ # A ⌞ ≤⁻ ⌝ ‶ X


s-refl-∞ : SRegular Γ
         → Γ ⊢r A
         → Γ ⊢ `□ # A ⌞ ≤ ⌝ A
s-refl-∞ regΓ ⊢r-int = s-int regΓ
s-refl-∞ regΓ (⊢r-var-∙ inΓ) = s-var-∙ regΓ inΓ
s-refl-∞ regΓ (⊢r-arr regA regA₁) = s-arr₁ (s-refl-∞ regΓ regA) (s-refl-∞ regΓ regA₁)
s-refl-∞ regΓ (⊢r-∀ regA) = s-∀ (s-refl-∞ (reg-S∙ regΓ) regA)

----------------------------------------------------------------------
--+                             Typing                             +--
----------------------------------------------------------------------

infix 3 _⊢_#_⦂_
data _⊢_#_⦂_ : Env n m → Mask → Term n m → Type m → Set where
  ⊢lit : ∀ {num : ℕ}
    → (regΓ : TRegular Γ)
    → Γ ⊢ `■ # (lit num) ⦂ Int
  ⊢var :
      (regΓ : TRegular Γ)
    → (x∈Γ : Γ ∋ x ⦂ A)
    → Γ ⊢ `■ # ` x ⦂ A
  ⊢ann :
      Γ ⊢ `□ # e ⦂ A
    → Γ ⊢ `■ # (e ⦂ A) ⦂ A
  ⊢lam₁ :
      Γ , A ⊢ `□ # e ⦂ B
    → Γ ⊢ `□ # ƛ e ⦂ A `→ B
  ⊢lam₂ :
      Γ , A ⊢ j # e ⦂ B
    → Γ ⊢ □ · j # ƛ e ⦂ A `→ B
  ⊢app :
      Γ ⊢ (fp i) · j # e₁ ⦂ A `→ B
    → Γ ⊢ (` i) # e₂ ⦂ A
    → Γ ⊢ j # e₁ · e₂ ⦂ B
  ⊢sub :
      Γ ⊢ `■ # g ⦂ A
    → (B≤A : Γ ⋈ ⊢ j # A ⌞ ≤⁺ ⌝ B)
    → (gc : GenericConsumer g)
    → (j≢Z : NonZ j)
    → Γ ⊢ j # g ⦂ B
  ⊢tabs :
      Γ ,∙ ⊢ (` i) # e ⦂ A
    → Γ ⊢ (` i) # Λ e ⦂ `∀ A
  ⊢tapp : Γ ⊢ `■ # e ⦂ `∀ B
        → (regA : Γ ⊢r A)
        → (st : ⟦ A ⟧ B ⇘ B*)
        → (s : Γ ⋈ ⊢ j # B* ⌞ ≤⁺ ⌝ C)
        → Γ ⊢ j # e ⓪ A ⦂ C
