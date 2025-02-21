module Implicit.Decl.Base where

open import Implicit.Language.All

----------------------------------------------------------------------
--+                           Subtyping                            +--
----------------------------------------------------------------------

infix 3 _⊢_#_≤_
data _⊢_#_≤_ : Env n m → Counter → Type m → Type m → Set where
  s-refl :
      (cloΓ : Norm Γ)
    → (cloA : Γ ⊢n A)
    → Γ ⊢ Z # A ≤ A
  s-int :
      (cloΓ : Norm Γ)
    → Γ ⊢ ∞ # Int ≤ Int
  s-var-∙ :
      (cloΓ : Norm Γ)
    → (inΓ : Γ ∋∙ X)
    → Γ ⊢ ∞ # ‶ X ≤ ‶ X
  s-arr₁ :
      Γ ⊢ ∞ # C ≤ A
    → Γ ⊢ ∞ # B ≤ D
    → Γ ⊢ ∞ # A `→ B ≤ C `→ D
  s-arr₂ :
      Γ ⊢ ∞ # C ≤ A
    → Γ ⊢ j # B ≤ D
    → Γ ⊢ 𝕚 j # A `→ B ≤ C `→ D
  s-arr₃ :
      (cloA : Γ ⊢n A)
    → Γ ⊢ j # B ≤ D
    → Γ ⊢ 𝕔 j # A `→ B ≤ A `→ D
  s-∀ :
      Γ ,∙ ⊢ ∞ # A ≤ B
    → Γ ⊢ ∞ # `∀ A ≤ `∀ B
  s-∀l :
      ⟦ B ⟧ A ⇘ A*
    → Γ ⊢ j # A* ≤ C `→ D
  -- we guess a solution of B here, we must make sure this B is provided from the counter
  -- what we does is to make sure the all inputs matching the counter should at least have the quantifer contained
    → (ic : (𝕚𝕔 j))
    → (fd : find A #0 j)
    → Γ ⊢ j # `∀ A ≤ C `→ D


----------------------------------------------------------------------
--+                             Typing                             +--
----------------------------------------------------------------------

infix 3 _⊢_#_⦂_
data _⊢_#_⦂_ : Env n m → Counter → Term n m → Type m → Set where
  ⊢lit : ∀ {num : ℕ}
    → (cloΣ : Norm Γ)
    → Γ ⊢ Z # (lit num) ⦂ Int
  ⊢var :
      (cloΣ : Norm Γ)
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
      Γ ⊢ Z # e ⦂ A
    → (B≤A : Γ ⊢ j # A ≤ B)
    → (j≢Z : NonZ j)
    → Γ ⊢ j # e ⦂ B
  ⊢tabs :
      Γ ,∙ ⊢ Z # e ⦂ A
    → Γ ⊢ Z # Λ e ⦂ `∀ A

-- small note: e @ A must be inferreable, and in the form of
-- (e @ A) e', e' could only be checked
