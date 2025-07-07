module Implicit.Interm.Base where

open import Implicit.Language.All

----------------------------------------------------------------------
--+                           Subtyping                            +--
----------------------------------------------------------------------

infix 3 _⊢_#_⌞_⌝_
data _⊢_#_⌞_⌝_ : Env n m → Counter m → Type m → Polar → Type m → Set where
  s-refl :
      (regΔ : SRegular Δ)
    → (cloA : Δ ⊢c A)
    → (grd : Δ ≫ A ⇘ A%)
    → Δ ⊢ Z # A ⌞ ≤⁺ ⌝ A%
  s-int :
      (regΔ : SRegular Δ)
    → Δ ⊢ ∞ # Int ⌞ ≤ ⌝ Int
  s-top+ :
      (regΔ : SRegular Δ)
    → (Δ ⊢c A)
    → Δ ⊢ ∞ # A ⌞ ≤⁺ ⌝ Top
  s-top- :
      (regΔ : SRegular Δ)
    → (regA : Δ ⊢r A)
    → Δ ⊢ ∞ # A ⌞ ≤⁻ ⌝ Top
  s-bot+ :
      (regΔ : SRegular Δ)
    → (regA : Δ ⊢r A)
    → Δ ⊢ ∞ # Bot ⌞ ≤⁺ ⌝ A
  s-bot- :
      (regΔ : SRegular Δ)
    → (regA : Δ ⊢c A)
    → Δ ⊢ ∞ # Bot ⌞ ≤⁻ ⌝ A
  s-var-∙ :
      (regΔ : SRegular Δ)
    → (inΔ : Δ ∋∙ X)
    → Δ ⊢ ∞ # ‶ X ⌞ ≤ ⌝ ‶ X
  s-arr₁ :
      Δ ⊢ ∞ # C ⌞ ⋆ ≤ ⌝ A
    → Δ ⊢ ∞ # B ⌞ ≤ ⌝ D
    → Δ ⊢ ∞ # A `→ B ⌞ ≤ ⌝ C `→ D
  s-arr₂ :
      Δ ⊢ ∞ # C ⌞ ≤⁻ ⌝ A
    → Δ ⊢ j # B ⌞ ≤⁺ ⌝ D
    → Δ ⊢ 𝕚 j # A `→ B ⌞ ≤⁺ ⌝ C `→ D
  s-arr₃ :
      (cloA : Δ ⊢c A)
    → (grd : Δ ≫ A ⇘ A%)
    → Δ ⊢ j # B ⌞ ≤⁺ ⌝ D
    → Δ ⊢ 𝕔 j # A `→ B ⌞ ≤⁺ ⌝ A% `→ D
  s-∀ :
      Δ ,∙ ⊢ ∞ # A ⌞ ≤ ⌝ B
    → Δ ⊢ ∞ # `∀ A ⌞ ≤ ⌝ `∀ B
  s-∀l :
      Δ ,= B ⊢ j' # A ⌞ ≤⁺ ⌝ C' `→ D'
    → (ic : (𝕚𝕔 j))
    → (fd : find A #0 j')
    → (upC : ↑ty0 C ⇘ C')
    → (upD : ↑ty0 D ⇘ D')
    → (upj : ↑tyʲ0 j ⇘ j')
    → Δ ⊢ j # `∀ A ⌞ ≤⁺ ⌝ C `→ D
  s-∀l-no-appear :
      Δ ,^ ⊢ j' # A ⌞ ≤⁺ ⌝ C' `→ D'
    → (ic : (𝕚𝕔 j))
    → (fd : #0 ¬ε A)
    → (upC : ↑ty0 C ⇘ C')
    → (upD : ↑ty0 D ⇘ D')
    → (upj : ↑tyʲ0 j ⇘ j')
    → Δ ⊢ j # `∀ A ⌞ ≤⁺ ⌝ C `→ D
  s-tapp :
      Δ ,= B ⊢ j' # A ⌞ ≤⁺ ⌝ C
    → (upj : ↑tyʲ0 j ⇘ j')
    → Δ ⊢ 𝕥₍ B ₎ j # `∀ A ⌞ ≤⁺ ⌝ `∀ C
  -- two atomic rules
  s-svar-l : ∀ {X A}
    → (inΔ : Δ ∋ X := A)
    → Δ ⊢ ∞ # A ⌞ ≤⁺ ⌝ B
    → Δ ⊢ ∞ # ‶ X ⌞ ≤⁺ ⌝ B
  s-svar-r : ∀ {X A}
    → (inΔ : Δ ∋ X := A)
    → Δ ⊢ ∞ # B ⌞ ≤⁻ ⌝ A
    → Δ ⊢ ∞ # B ⌞ ≤⁻ ⌝ ‶ X
  s-svar-𝕚 :
      Δ ∋ X := C
    → Δ ⊢ (𝕚 j) # C ⌞ ≤⁺ ⌝ A `→ B
    → Δ ⊢ (𝕚 j) # ‶ X ⌞ ≤⁺ ⌝ A `→ B
  s-svar-𝕔 :
      Δ ∋ X := C
    → Δ ⊢ (𝕔 j) # C ⌞ ≤⁺ ⌝ A `→ B
    → Δ ⊢ (𝕔 j) # ‶ X ⌞ ≤⁺ ⌝ A `→ B
  s-svar-𝕥 :
      Δ ∋ X := B
    → Δ ⊢ (𝕥₍ A ₎ j) # B ⌞ ≤⁺ ⌝ `∀ C
    → Δ ⊢ (𝕥₍ A ₎ j) # ‶ X ⌞ ≤⁺ ⌝ `∀ C

s-refl-∞ : SRegular Γ
         → Γ ⊢r A
         → Γ ⊢ ∞ # A ⌞ ≤ ⌝ A
s-refl-∞ regΓ ⊢r-int = s-int regΓ
s-refl-∞ {≤ = ≤⁺} x ⊢r-top = s-top+ x ⊢c-top
s-refl-∞ {≤ = ≤⁻} x ⊢r-top = s-top- x ⊢r-top
s-refl-∞ regΓ (⊢r-var-∙ inΓ) = s-var-∙ regΓ inΓ
s-refl-∞ regΓ (⊢r-arr regA regA₁) = s-arr₁ (s-refl-∞ regΓ regA) (s-refl-∞ regΓ regA₁)
s-refl-∞ regΓ (⊢r-∀ regA) = s-∀ (s-refl-∞ (reg-S∙ regΓ) regA)
s-refl-∞ {≤ = ≤⁺} regΓ ⊢r-bot = s-bot+ regΓ ⊢r-bot
s-refl-∞ {≤ = ≤⁻} regΓ ⊢r-bot = s-bot- regΓ ⊢c-bot

----------------------------------------------------------------------
--+                             Typing                             +--
----------------------------------------------------------------------

infix 3 _⊢_#_⦂_
data _⊢_#_⦂_ : Env n m → Counter m → Term n m → Type m → Set where
  ⊢lit : ∀ {num : ℕ}
    → (regΓ : TRegular Γ)
    → Γ ⊢ Z # (lit num) ⦂ Int
  ⊢var :
      (regΓ : TRegular Γ)
    → (x∈Γ : Γ ∋ x ⦂ A)
    → Γ ⊢ Z # ` x ⦂ A
  ⊢ann :
      Γ ⊢ ∞ # e ⦂ A
    → Γ ⊢ Z # (e ⦂ A) ⦂ A
  ⊢lam₁ :
      Γ , A ⊢ ∞ # e ⦂ B
    → Γ ⊢ ∞ # ƛ e ⦂ A `→ B
  ⊢lam₂ :
      Γ , A ⊢ j # e ⦂ B
    → Γ ⊢ 𝕚 j # ƛ e ⦂ A `→ B
  ⊢app₁ :
      Γ ⊢ 𝕔 j # e₁ ⦂ A `→ B
    → Γ ⊢ ∞ # e₂ ⦂ A
    → Γ ⊢ j # e₁ · e₂ ⦂ B
  ⊢app₂ :
      Γ ⊢ 𝕚 j # e₁ ⦂ A `→ B
    → Γ ⊢ Z # e₂ ⦂ A
    → Γ ⊢ j # e₁ · e₂ ⦂ B
  ⊢sub :
      Γ ⊢ Z # g ⦂ A
    → (B≤A : Γ ⋈ ⊢ j # A ⌞ ≤⁺ ⌝ B)
    → (gc : GenericConsumer g)
    → (j≢Z : NonZ j)
    → Γ ⊢ j # g ⦂ B
  ⊢tabs :
      Γ ,∙ ⊢ Z # e ⦂ A
    → Γ ⊢ Z # Λ e ⦂ `∀ A
  ⊢tapp : Γ ⊢ 𝕥₍ A ₎ j # e ⦂ `∀ B
        → (st : ⟦ A ⟧ B ⇘ B*)
        → Γ ⊢ j # e ⓪ A ⦂ B*


-- _ : ∅ , `∀ (‶ #0 `→ ‶ #0 `→ ‶ #0) , Top ⊢ Z # (` #1) · (lit 1) · (` #0) ⦂ Top
