module Implicit.Language.Regular.Base where

open import Implicit.Language.Base
open import Implicit.Language.Lookup.Base

-- a regular type, just like system-f types
infix 3 _⊢r_
data _⊢r_ : Env n m → Type m → Set where
  ⊢r-int :
      Γ ⊢r Int
  ⊢r-top :
      Γ ⊢r Top
  ⊢r-bot :
      Γ ⊢r Bot
  ⊢r-var-∙ :
      (inΓ : Γ ∋∙ X)
    → Γ ⊢r ‶ X
  ⊢r-arr :
      Γ ⊢r A
    → Γ ⊢r B
    → Γ ⊢r (A `→ B)
  ⊢r-∀ :
      Γ ,∙ ⊢r A
    → Γ ⊢r `∀ A

infix 3 _⊢rᵉ_
data _⊢rᵉ_ : Env n m → Term n m → Set where
  ⊢r-lit : ∀ {num} → Γ ⊢rᵉ (lit num)
  ⊢r-var : Γ ⊢rᵉ (` x)
  ⊢r-lam : Γ , A ⊢rᵉ e
         → Γ ⊢rᵉ (ƛ e)
  ⊢r-app : Γ ⊢rᵉ e₁ → Γ ⊢rᵉ e₂ → Γ ⊢rᵉ (e₁ · e₂)
  ⊢r-ann : (cloA : Γ ⊢r A) → Γ ⊢rᵉ e → Γ ⊢rᵉ (e ⦂ A)
  ⊢r-tlam : Γ ,∙ ⊢rᵉ e → Γ ⊢rᵉ (Λ e)

data TRegular : Env n m → Set where
  reg-Z : TRegular ∅
  reg-S, : TRegular Γ
         → (regA : Γ ⊢r A)
         → TRegular (Γ , A)
  reg-S∙ : TRegular Γ
         → TRegular (Γ ,∙)
  reg-S^ : TRegular Γ
         → TRegular (Γ ,^)
  reg-S= : TRegular Γ
         → (regA : Γ ⊢r A) -- we never access this entry, it's only created by initials
         → TRegular (Γ ,= A)

data SRegular : Env n m → Set where
  reg-Z : (regΓ : TRegular Γ)
        → SRegular (Γ ⋈)
  reg-S∙ : SRegular Δ
         → SRegular (Δ ,∙)
  reg-S^ : SRegular Δ
         → SRegular (Δ ,^)
  reg-S= : SRegular Δ
         → (regA : Δ ⊢r A)
         → SRegular (Δ ,= A)
