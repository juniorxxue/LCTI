module Implicit.SimCounter.Typing where

open import Implicit.Language.All
open import Implicit.SimCounter.Subtyping2

infix 3 _⊨_#_⦂_
data _⊨_#_⦂_ : Env n m → SCounter → Term n m → Type m → Set where
  ⊨lit : ∀ {num : ℕ}
    → (regΓ : TRegularS Γ)
    → Γ ⊨ Z # (lit num) ⦂ Int
  ⊨var :
      (regΓ : TRegularS Γ)
    → (x∈Γ : Γ ∋ x ⦂ A)
    → Γ ⊨ Z # ` x ⦂ A
  ⊨ann :
      Γ ⊨ ∞ # e ⦂ A
    → Γ ⊨ Z # (e ⦂ A) ⦂ A
  ⊨lam₁ :
      Γ , A ⊨ ∞ # e ⦂ B
    → Γ ⊨ ∞ # ƛ e ⦂ A `→ B
  ⊨lam₂ :
      Γ , A ⊨ 𝕟 # e ⦂ B
    → Γ ⊨ 𝕚 𝕟 # ƛ e ⦂ A `→ B
  ⊨app₁ :
      Γ ⊨ 𝕔 𝕟 # e₁ ⦂ A `→ B
    → Γ ⊨ ∞ # e₂ ⦂ A
    → Γ ⊨ 𝕟 # e₁ · e₂ ⦂ B
  ⊨app₂ :
      Γ ⊨ 𝕚 𝕟 # e₁ ⦂ A `→ B
    → Γ ⊨ Z # e₂ ⦂ A
    → Γ ⊨ 𝕟 # e₁ · e₂ ⦂ B
  ⊨sub :
      Γ ⊨ Z # g ⦂ A
    → (B≤A : Γ ⋈ ⊨ 𝕟 # A ⌞ ≤⁺ ⌝ B)
    → (gc : GenericConsumer g)
    → (𝕟≢Z : SNonZ 𝕟)
    → Γ ⊨ 𝕟 # g ⦂ B
  ⊨tabs :
      Γ ,∙ ⊨ Z # e ⦂ A
    → Γ ⊨ Z # Λ e ⦂ `∀ A
  ⊨tapp :
      Γ ⊨ 𝕥 𝕟 # e ⦂ `∀ B
    → (st : ⟦ A ⟧ B ⇘ B*)
    → (regA : Γ ⊢t A)
    → Γ ⊨ 𝕟 # e ⓪ A ⦂ B*
