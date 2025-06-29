module Implicit.SimCounter.Completeness.Interm where

open import Implicit.Language.All
open import Implicit.AuxLemmas
open import Implicit.SimCounter.Subtyping2

infix 3 _⊢_#_⌞_⌝_
data _⊢_#_⌞_⌝_ : Env n m → Counter m → Type m → Polar → Type m → Set where
  s-refl :
      (regΔ : SRegularS Δ)
    → (cloA : Δ ⊢c A)
    → (grd : Δ ≫ A ⇘ A%)
    → Δ ⊢ Z # A ⌞ ≤⁺ ⌝ A%
  s-int :
      (regΔ : SRegularS Δ)
    → Δ ⊢ ∞ # Int ⌞ ≤ ⌝ Int
  s-var-∙ :
      (regΔ : SRegularS Δ)
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
    → (SRegularS Δ)
    → (inΔ : Δ ∋ X := A)
    → Δ ⊢ ∞ # ‶ X ⌞ ≤⁺ ⌝ A
  s-svar-r : ∀ {X A}
    → (SRegularS Δ)
    → (inΔ : Δ ∋ X := A)
    → Δ ⊢ ∞ # A ⌞ ≤⁻ ⌝ ‶ X
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
