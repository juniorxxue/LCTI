module Implicit.SimCounter.IntermEla where

open import Implicit.Language.All

----------------------------------------------------------------------
--+                           Subtyping                            +--
----------------------------------------------------------------------

variable
  A✦ B✦ C✦ D✦ : Type m

infix 3 _≫_⇘_↡_
data _≫_⇘_↡_ : Env n m → Type m → Type m → Type m → Set
data _≫_⇘_↡_ where
  grd-int : Δ ≫ Int ⇘ Int ↡ Int
  grd-var= : Δ ∋ X := A
           → Δ ≫ (‶ X) ⇘ A ↡ (‶ X)
  grd-var∙ : Δ ∋∙ X
          → Δ ≫ (‶ X) ⇘ (‶ X) ↡ (‶ X)
  grd-arr : Δ ≫ A ⇘ A% ↡ A'
          → Δ ≫ B ⇘ B% ↡ B'
          → Δ ≫ (A `→ B) ⇘ A% `→ B% ↡ A✦ `→ B✦
  grd-∀   : Δ ,∙ ≫ A ⇘ A% ↡ A✦
          → Δ ≫ `∀ A ⇘ `∀ A% ↡ `∀ A✦

infix 3 _⊢_#_⌞_⌝_↡_
data _⊢_#_⌞_⌝_↡_ : Env n m → Counter m → Type m → Polar → Type m → Type m → Set where
  s-refl :
      (regΔ : SRegular Δ)
    → (cloA : Δ ⊢c A)
    → (grd : Δ ≫ A ⇘ A% ↡ A✦)
    → Δ ⊢ Z # A ⌞ ≤⁺ ⌝ A% ↡ A✦
  s-int :
      (regΔ : SRegular Δ)
    → Δ ⊢ ∞ # Int ⌞ ≤ ⌝ Int ↡ Int
  s-var-∙ :
      (regΔ : SRegular Δ)
    → (inΔ : Δ ∋∙ X)
    → Δ ⊢ ∞ # ‶ X ⌞ ≤ ⌝ ‶ X ↡ ‶ X
  s-arr₁ :
      Δ ⊢ ∞ # C ⌞ ⋆ ≤ ⌝ A ↡ C✦
    → Δ ⊢ ∞ # B ⌞ ≤ ⌝ D ↡ D✦
    → Δ ⊢ ∞ # A `→ B ⌞ ≤ ⌝ C `→ D ↡ C✦ `→ D✦
  s-arr₂ :
      Δ ⊢ ∞ # C ⌞ ≤⁻ ⌝ A ↡ C✦
    → Δ ⊢ j # B ⌞ ≤⁺ ⌝ D ↡ D✦
    → Δ ⊢ 𝕚 j # A `→ B ⌞ ≤⁺ ⌝ C `→ D ↡ C✦ `→ D✦
  s-arr₃ :
      (cloA : Δ ⊢c A)
    → (grd : Δ ≫ A ⇘ A% ↡ A✦)
    → Δ ⊢ j # B ⌞ ≤⁺ ⌝ D ↡ D✦
    → Δ ⊢ 𝕔 j # A `→ B ⌞ ≤⁺ ⌝ A% `→ D ↡ A✦ `→ D✦
  s-∀ :
      Δ ,∙ ⊢ ∞ # A ⌞ ≤ ⌝ B ↡ B✦
    → Δ ⊢ ∞ # `∀ A ⌞ ≤ ⌝ `∀ B ↡ `∀ B✦
  s-∀l :
      Δ ⊢ j # A* ⌞ ≤⁺ ⌝ C `→ D ↡ C✦ `→ D✦
    → (ic : (𝕚𝕔 j))
    → (fd : find A #0 j')
    → (upj : ↑tyʲ0 j ⇘ j')
    → (st : ⟦ B ⟧ A ⇘ A*)
    → Δ ⊢ j # `∀ A ⌞ ≤⁺ ⌝ C `→ D ↡ C✦ `→ D✦
  s-∀l-no-appear :
      Δ ⊢ j # A* ⌞ ≤⁺ ⌝ C `→ D ↡ C✦ `→ D✦
    → (ic : (𝕚𝕔 j))
    → (fd : #0 ¬ε A)
    → (upj : ↑tyʲ0 j ⇘ j')
    → (st : ⟦ B ⟧ A ⇘ A*)
    → Δ ⊢ j # `∀ A ⌞ ≤⁺ ⌝ C `→ D  ↡ C✦ `→ D✦
  s-tapp :
      Δ ,= B ⊢ j' # A ⌞ ≤⁺ ⌝ C ↡ C✦
    → (upj : ↑tyʲ0 j ⇘ j')
    → Δ ⊢ 𝕥₍ B ₎ j # `∀ A ⌞ ≤⁺ ⌝ `∀ C ↡ `∀ C✦
  s-svar-l : ∀ {X A}
    → (SRegular Δ)
    → (inΔ : Δ ∋ X := A)
    → Δ ⊢ ∞ # ‶ X ⌞ ≤⁺ ⌝ A ↡ ‶ X
  s-svar-r : ∀ {X A}
    → (SRegular Δ)
    → (inΔ : Δ ∋ X := A)
    → Δ ⊢ ∞ # A ⌞ ≤⁻ ⌝ ‶ X ↡ ‶ X
  s-svar-𝕚 :
      Δ ∋ X := C
    → Δ ⊢ (𝕚 j) # C ⌞ ≤⁺ ⌝ A `→ B ↡ D✦
    → Δ ⊢ (𝕚 j) # ‶ X ⌞ ≤⁺ ⌝ A `→ B ↡ ‶ X
  s-svar-𝕔 :
      Δ ∋ X := C
    → Δ ⊢ (𝕔 j) # C ⌞ ≤⁺ ⌝ A `→ B ↡ D✦
    → Δ ⊢ (𝕔 j) # ‶ X ⌞ ≤⁺ ⌝ A `→ B ↡ ‶ X
  s-svar-𝕥 :
      Δ ∋ X := B
    → Δ ⊢ (𝕥₍ A ₎ j) # B ⌞ ≤⁺ ⌝ `∀ C ↡ D✦
    → Δ ⊢ (𝕥₍ A ₎ j) # ‶ X ⌞ ≤⁺ ⌝ `∀ C ↡ ‶ X
