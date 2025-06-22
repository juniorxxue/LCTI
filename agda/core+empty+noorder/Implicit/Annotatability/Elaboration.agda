module Implicit.Annotatability.Elaboration where

open import Implicit.Language.All


infix 3 _⊢_𝕄_
data _⊢_𝕄_ : Env n m → Type m → Type m → Set where
  𝕄-arr : Γ ⊢ A `→ B 𝕄 A `→ B
  M-∀ : Γ ⊢r T
      → (st : ⟦ T ⟧ A ⇘ A*)
      → Γ ⊢ A* 𝕄 B `→ C
      → Γ ⊢ `∀ A 𝕄 B `→ C

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
           → Γ ⊢ A 𝕄 B `→ C
           → Γ ⊢ e₂ ⦂ B ⟶ e₂'
           → Γ ⊢ e₁ · e₂ ⦂ C ⟶ e₁' · (e₂' ⦂ B)
  -- two extra rules
  ela-∀i  : Γ ,∙ ⊢ e' ⦂ A ⟶ e₁
         → (upe : ↑tyᵉ0 e ⇘ e')
         → Γ ⊢ e ⦂ `∀ A ⟶ Λ (e₁ ⦂ A)
  ela-∀e  : Γ ⊢ e ⦂ `∀ A ⟶ e'
          → ⟦ B ⟧ A ⇘ A*
          → Γ ⊢r B
          → Γ ⊢ e ⦂ A* ⟶ e' ⓪ B


ela-tregular : Γ ⊢ e ⦂ A ⟶ e'
             → TRegular Γ
ela-tregular (ela-lit regΓ) = regΓ
ela-tregular (ela-var regΓ x) = regΓ
ela-tregular (ela-lam s) with ela-tregular s
... | reg-S, r regA = r
ela-tregular (ela-app s x s₁) = ela-tregular s
ela-tregular (ela-∀i s upe) with ela-tregular s
... | reg-S∙ r = r
ela-tregular (ela-∀e s x regB) = ela-tregular s


𝕄-⊢r : Γ ⊢r A
     → Γ ⊢ A 𝕄 B
     → Γ ⊢r B
𝕄-⊢r (⊢r-arr regA regA₁) 𝕄-arr = ⊢r-arr regA regA₁
𝕄-⊢r (⊢r-∀ regA) (M-∀ x st mm) = 𝕄-⊢r (st0-⊢r (⊢r-∀ regA) x st) mm

ela-⊢r : Γ ⊢ e ⦂ A ⟶ e'
       → Γ ⊢r A
ela-⊢r (ela-lit regΓ) = ⊢r-int
ela-⊢r (ela-var regΓ x) = ∋⦂-⊢r regΓ x
ela-⊢r (ela-lam ⊢e) with ela-tregular ⊢e
... | reg-S, r regA = ⊢r-arr regA (⊢r-strengthen,0 (ela-⊢r ⊢e))
ela-⊢r (ela-app ⊢e x ⊢e₁) with 𝕄-⊢r (ela-⊢r ⊢e) x
... | ⊢r-arr r r₁ = r₁
ela-⊢r (ela-∀i ⊢e upe) = ⊢r-∀ (ela-⊢r ⊢e)
ela-⊢r (ela-∀e ⊢e x regB) = st0-⊢r (ela-⊢r ⊢e) regB x
