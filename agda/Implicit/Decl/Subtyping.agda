module Implicit.Decl.Subtyping where

open import Implicit.Language.All

----------------------------------------------------------------------
--+                           Subtyping                            +--
----------------------------------------------------------------------

infix 3 _⊢_#_⌞_⌝_
data _⊢_#_⌞_⌝_ : Env n m → Counter m → Type m → Polar → Type m → Set where
  s-refl :
      (regΔ : SRegular Δ)
    → (cloA : Δ ⊢r A)
    → Δ ⊢ Z # A ⌞ ≤⁺ ⌝ A
  s-int :
      (regΔ : SRegular Δ)
    → Δ ⊢ ∞ # Int ⌞ ≤ ⌝ Int
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
      (regA : Δ ⊢r A)
    → Δ ⊢ j # B ⌞ ≤⁺ ⌝ D
    → Δ ⊢ 𝕔 j # A `→ B ⌞ ≤⁺ ⌝ A `→ D
  s-∀ :
      Δ ,∙ ⊢ ∞ # A ⌞ ≤ ⌝ B
    → Δ ⊢ ∞ # `∀ A ⌞ ≤ ⌝ `∀ B
  s-∀l :
      (regB : Γ ⊢r B)
    → (st : ⟦ B ⟧ A ⇘ A*)
    → Γ ⊢ j # A* ⌞ ≤⁺ ⌝ C `→ D
    → (ic : (𝕚𝕔 j))
    → (fd : find A #0 j')
    → (upj : ↑tyʲ0 j ⇘ j')
    → Γ ⊢ j # `∀ A ⌞ ≤⁺ ⌝ C `→ D
  s-tapp :
      (regB : Δ ⊢r B)
    → (st : ⟦ B ⟧ A ⇘ A*)
    → Δ ⊢ j # A* ⌞ ≤⁺ ⌝ C
    → (upC : ↑ty0 C ⇘ C')
    → Δ ⊢ 𝕥₍ B ₎ j # `∀ A ⌞ ≤⁺ ⌝ `∀ C'


postulate
  s1-⊢r-l : Γ ⊢ j # A ⌞ ≤ ⌝ B
        → Γ ⊢r A


  s1-strengthen=0 : Γ ,= T ⊢ j' # A' ⌞ ≤ ⌝ B'
            → ↑ty0 A ⇘ A'
            → ↑ty0 B ⇘ B'
            → ↑tyʲ0 j ⇘ j'
            → Γ ⊢ j # A ⌞ ≤ ⌝ B
