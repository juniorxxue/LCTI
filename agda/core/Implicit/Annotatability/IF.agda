module Implicit.Annotatability.IF where

open import Implicit.Language.All

-- not occur only at the end
infix 3 _¬ε'_
data _¬ε'_ : Fin m → Type m → Set where
  ¬ε'-int : k ¬ε' Int
  ¬ε'-var : k ≢ X
          → k ¬ε' ‶ X
  ¬ε'-arr-l : k ε A
          → k ¬ε' (A `→ B)
  ¬ε'-arr-r : k ¬ε A
            → k ¬ε' B
            → k ¬ε' (A `→ B)
  ¬ε'-∀ : #S k ¬ε' A
        → k ¬ε' (`∀ A)

infix 3 _⟾_
data _⟾_ : Type m → Type m → Set where
  ⟾-arr : A `→ B ⟾ A `→ B
  M-∀ : (st : ⟦ T ⟧ A ⇘ A*)
       → A* ⟾ B `→ C
       → (rst : #0 ¬ε' A)
       → `∀ A ⟾ B `→ C

infix 3 _⊢_⟾_
data _⊢_⟾_ : Env n m → Type m → Type m → Set where
  ⟾-arr : Γ ⊢ A `→ B ⟾ A `→ B
  ⟾-∀ : Γ ⊢r T
      → (st : ⟦ T ⟧ A ⇘ A*)
      → Γ ⊢ A* ⟾ B `→ C
      → Γ ⊢ `∀ A ⟾ B `→ C

infix 3 _⊢_⦂_⟶_
data _⊢_⦂_⟶_ : Env n m → Term n m → Type m → Term n m → Set where

  ela-lit : (regΓ : TRegular Γ)
          → Γ ⊢ (lit n) ⦂ Int ⟶ (lit n)
  ela-var : (regΓ : TRegular Γ)
          → Γ ∋ x ⦂ A
          → Γ ⊢ ` x ⦂ A ⟶ ` x
  ela-lam : Γ , A ⊢ e ⦂ B ⟶ e'
          → Γ ⊢ ƛ e ⦂ A `→ B ⟶ ƛ e'
  ela-app : Γ ⊢ e₁ ⦂ A ⟶ e₁'
           → Γ ⊢ A ⟾ B `→ C
           → Γ ⊢ e₂ ⦂ B ⟶ e₂'
           → Γ ⊢ e₁ · e₂ ⦂ C ⟶ e₁' · (e₂' ⦂ B)
{-
  ela-∀ : Γ ,∙ ⊢ e' ⦂ A ⟶ e₁
        → (up-e : ↑tyᵉ0 e ⇘ e')
        → Γ ⊢ e ⦂ `∀ A ⟶ Λ e₁
-}
