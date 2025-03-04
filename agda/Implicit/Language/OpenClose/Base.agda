module Implicit.Language.OpenClose.Base where

open import Implicit.Language.Base
open import Implicit.Language.Lookup.All

-- used in s-term-o rule, there're some variables in subtyping environment unsolved
infix 3 _⊢o²_
data _⊢o²_ :  Env n m → Type m → Set where
  ⊢o²-var-^ :
      Γ ∋^² X
    → Γ ⊢o² ‶ X
  ⊢o²-arr-l :
      Γ ⊢o² A
    → Γ ⊢o² (A `→ B)
  ⊢o²-arr-r :
      Γ ⊢o² B
    → Γ ⊢o² (A `→ B)
  ⊢o²-∀ :
      Γ ,∙ ⊢o² A
    → Γ ⊢o² `∀ A

-- used in polarity interpretation, Γ ⊢c¹ A means, type variables in A
-- 1. universal var: it can be in typing and subtyping
-- 2. ex var: it cannot have ex-var
-- 3. solution: it can only be in typing

infix 3 _⊢c¹_
data _⊢c¹_ : Env n m → Type m → Set where
  ⊢c¹-int :
      Γ ⊢c¹ Int
  ⊢c¹-var-∙ :
      (inΓ : Γ ∋∙ X)
    → Γ ⊢c¹ ‶ X
  ⊢c¹-arr :
      Γ ⊢c¹ A
    → Γ ⊢c¹ B
    → Γ ⊢c¹ (A `→ B)
  ⊢c¹-∀ :
      Γ ,∙ ⊢c¹ A
    → Γ ⊢c¹ `∀ A

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

infix 3 _⊢c_
data _⊢c_ : Env n m → Type m → Set where
  ⊢c-int :
      Γ ⊢c Int
  ⊢c-var-∙ :
      (inΓ : Γ ∋∙ X)
    → Γ ⊢c ‶ X
  ⊢c-var-= :
      (inΓ : Γ ∋=¹ X)
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

infix 3 _⊢cᵉ¹_
data _⊢cᵉ¹_ : Env n m → Term n m → Set where
  ⊢c-lit : ∀ {num} → Γ ⊢cᵉ¹ (lit num)
  ⊢c-var : Γ ⊢cᵉ¹ (` x)
  ⊢c-lam : Γ , A ⊢cᵉ¹ e
         → Γ ⊢cᵉ¹ (ƛ e)
  ⊢c-app : Γ ⊢cᵉ¹ e₁ → Γ ⊢cᵉ¹ e₂ → Γ ⊢cᵉ¹ (e₁ · e₂)
  ⊢c-ann : (cloA : Γ ⊢c¹ A) → Γ ⊢cᵉ¹ e → Γ ⊢cᵉ¹ (e ⦂ A)
  ⊢c-tlam : Γ ,∙ ⊢cᵉ¹ e → Γ ⊢cᵉ¹ (Λ e)


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
  clo-S⋈ : Closed Γ
         → Closed (Γ ⋈)

data TypClosed : Env n m → Set where
  clo-Z : TypClosed ∅
  clo-S, : TypClosed Γ
         → (cloA : Γ ⊢c¹ A)
         → TypClosed (Γ , A)
  clo-S∙ : TypClosed Γ
         → TypClosed (Γ ,∙)
  clo-S^ : TypClosed Γ
         → TypClosed (Γ ,^)
  clo-S= : TypClosed Γ
--         → (cloA : Γ ⊢c¹ A) -- we dont care, since we shouldn't access this entry, just skipping
         → TypClosed (Γ ,= A)

data SubClosed : Env n m → Set where
  clo-Z : TypClosed Γ
        → SubClosed (Γ ⋈)
  clo-S, : SubClosed Γ
         → (cloA : Γ ⊢c¹ A)
         → SubClosed (Γ , A)
  clo-S∙ : SubClosed Γ
         → SubClosed (Γ ,∙)
  clo-S^ : SubClosed Γ
         → SubClosed (Γ ,^)
  clo-S= : SubClosed Γ
         → (cloA : Γ ⊢c¹ A)
         → SubClosed (Γ ,= A)
