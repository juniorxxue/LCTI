module Implicit.Language.Norm.Base where
-- a strict version of close, where the allowable freevars are only universal variables

open import Implicit.Language.Base
open import Implicit.Language.Lookup.All

infix 3 _⊢n_
data _⊢n_ : Env n m → Type m → Set where
  ⊢n-int :
      Γ ⊢n Int
  ⊢n-var-∙ :
      (inΓ : Γ ∋∙ X)
    → Γ ⊢n ‶ X
  ⊢n-arr :
      Γ ⊢n A
    → Γ ⊢n B
    → Γ ⊢n (A `→ B)
  ⊢n-∀ :
      Γ ,∙ ⊢n A
    → Γ ⊢n `∀ A

infix 3 _⊢nᵉ_
data _⊢nᵉ_ : Env n m → Term n m → Set where
  ⊢n-lit : ∀ {num} → Γ ⊢nᵉ (lit num)
  ⊢n-var : Γ ⊢nᵉ (` x)
  ⊢n-lam : Γ , A ⊢nᵉ e
         → Γ ⊢nᵉ (ƛ e)
  ⊢n-app : Γ ⊢nᵉ e₁ → Γ ⊢nᵉ e₂ → Γ ⊢nᵉ (e₁ · e₂)
  ⊢n-ann : (cloA : Γ ⊢n A) → Γ ⊢nᵉ e → Γ ⊢nᵉ (e ⦂ A)
  ⊢n-tlam : Γ ,∙ ⊢nᵉ e → Γ ⊢nᵉ (Λ e)


data Norm : Env n m → Set where
  nom-Z : Norm ∅
  nom-S, : Norm Γ
         → (nrmA : Γ ⊢n A)
         → Norm (Γ , A)
  nom-S∙ : Norm Γ
         → Norm (Γ ,∙)
  nom-S^ : Norm Γ
         → Norm (Γ ,^)
  nom-S= : Norm Γ
         → (nomA : Γ ⊢n A)
         → Norm (Γ ,= A)
