module Implicit.Language.OpenClose.Base where

open import Implicit.Language.Base
open import Implicit.Language.Shift
open import Implicit.Language.Lookup

infix 3 _⊢c_
infix 3 _⊢o_

-- open: have free existential variables
data _⊢o_ : Env n m → Type m → Set where
  ⊢o-var-^ :
      Γ ∋^ X
    → Γ ⊢o ‶ X
  ⊢o-arr-l :
      Γ ⊢o A
    → Γ ⊢o (A `→ B)
  ⊢o-arr-r :
      Γ ⊢o B
    → Γ ⊢o (A `→ B)
  ⊢o-∀ :
      Γ ,∙ ⊢o A
    → Γ ⊢o `∀ A

data _⊢c_ : Env n m → Type m → Set where
  ⊢c-int :
      Γ ⊢c Int
  ⊢c-var-∙ :
      (inΓ : Γ ∋∙ X)
    → Γ ⊢c ‶ X
  ⊢c-var-= :
      (inΓ : Γ ∋= X)
    → Γ ⊢c ‶ X
  ⊢c-arr :
      Γ ⊢c A
    → Γ ⊢c B
    → Γ ⊢c (A `→ B)
  ⊢c-∀ :
      Γ ,∙ ⊢c A
    → Γ ⊢c `∀ A

infix 3 _⊢cᵉ_
data _⊢cᵉ_ : Env n m → Term n m → Set where
  ⊢c-lit : ∀ {num} → Γ ⊢cᵉ (lit num)
  ⊢c-var : Γ ⊢cᵉ (` x)
  ⊢c-lam : Γ , A ⊢cᵉ e
         → Γ ⊢cᵉ (ƛ e)
  ⊢c-app : Γ ⊢cᵉ e₁ → Γ ⊢cᵉ e₂ → Γ ⊢cᵉ (e₁ · e₂)
  ⊢c-ann : (cloA : Γ ⊢c A) → Γ ⊢cᵉ e → Γ ⊢cᵉ (e ⦂ A)
  ⊢c-tlam : Γ ,∙ ⊢cᵉ e → Γ ⊢cᵉ (Λ e)


data Closed : Env n m → Set where
  clo-Z : Closed ∅
  clo-S, : Closed Γ
         → (cloA : Γ ⊢c A)
         → Closed (Γ , A)
  clo-S∙ : Closed Γ
         → Closed (Γ ,∙)
  clo-S^ : Closed Γ
         → Closed (Γ ,^)
  clo-S= : Closed Γ
         → (cloA : Γ ⊢c A)
         → Closed (Γ ,= A)

-- closeness under certain positions
infix 3 _⊢cⁿ_by_
data _⊢cⁿ_by_ : Env n m → Type m → Fin (1 + n) → Set where
  clb-Z : (cloA : Γ ⊢c A)
        → Γ ⊢cⁿ A by #0

  clb-S, : Γ ⊢cⁿ A by k
         → Γ , T ⊢cⁿ A by #S k

  clb-S∙ : Γ ⊢cⁿ A by k
         → (up : ↑ty0 A ⇘ A')
         → Γ ,∙ ⊢cⁿ A' by k

  clb-S^ : Γ ⊢cⁿ A by k
         → (up : ↑ty0 A ⇘ A')
         → Γ ,^ ⊢cⁿ A' by k

  clb-S= : Γ ⊢cⁿ A by k
         → (up : ↑ty0 A ⇘ A')
         → Γ ,= T ⊢cⁿ A' by k

infix 3 _⊢cᵐ_by_
data _⊢cᵐ_by_ : Env n m → Type m → Fin (1 + m) → Set where
  clb-Z : (cloA : Γ ⊢c A)
        → Γ ⊢cᵐ A by #0

  clb-S, : Γ ⊢cᵐ A by k
         → Γ , T ⊢cᵐ A by k

  clb-S∙ : Γ ⊢cᵐ A by k
         → (up : ↑ty0 A ⇘ A')
         → Γ ,∙ ⊢cᵐ A' by #S k

  clb-S^ : Γ ⊢cᵐ A by k
         → (up : ↑ty0 A ⇘ A')
         → Γ ,^ ⊢cᵐ A' by #S k

  clb-S= : Γ ⊢cᵐ A by k
         → (up : ↑ty0 A ⇘ A')
         → Γ ,= T ⊢cᵐ A' by #S k
