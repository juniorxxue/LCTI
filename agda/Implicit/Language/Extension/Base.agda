module Implicit.Language.Extension.Base where

open import Implicit.Language.Base
open import Implicit.Language.Regular.Base
open import Implicit.Language.Lookup.Base

infix 3 _⊆_
data _⊆_ : Env n m → Env n m → Set where
  uvar :
      Γ ⊆ Δ
    → Γ ,∙ ⊆ Δ ,∙
  evar :
      Γ ⊆ Δ
    → Γ ,^ ⊆ Δ ,^
  evar-sol :
      Γ ⊆ Δ
    → (regA : Δ ⊢r A)
    → Γ ,^ ⊆ Δ ,= A
  svar :
      Γ ⊆ Δ
    → (regA : Γ ⊢r A)
    → Γ ,= A ⊆ Δ ,= A
  mark : TRegular Γ
    → Γ ⋈ ⊆ Γ ⋈

data ExSol (Γ : Env n m) (k : Fin m) : Set where
  is-ex  : (inΓ : Γ ∋^ k) → ExSol Γ k
  is-sol : (inΓ : Γ ∋= k) → ExSol Γ k

-- a more restricted extending

infix 3 _⊆_w/v_
data _⊆_w/v_ : Env n m → Env n m → Fin m → Set where
  ext-Z^ : (cloA : Γ ⊢r A)
         → Γ ,^ ⊆ Γ ,= A w/v #0
  ext-Z∙ : Γ ,∙ ⊆ Γ ,∙ w/v #0
  ext-S, : Γ ⊆ Δ w/v k
         → Γ , A ⊆ Δ , A w/v k
  ext-S^ : Γ ⊆ Δ w/v k
         → Γ ,^ ⊆ Δ ,^ w/v #S k
  ext-S∙ : Γ ⊆ Δ w/v k
         → Γ ,∙ ⊆ Δ ,∙ w/v #S k
  ext-S= : Γ ⊆ Δ w/v k
         → Γ ,= A ⊆ Δ ,= A w/v #S k
  ext-mark : TEnv Γ
         → Γ ⋈ ⊆ Γ ⋈ w/v k

infix 3 _⊆_w/t_
data _⊆_w/t_ : Env n m → Env n m → Type m → Set where
  ext-int : Γ ⊆ Γ w/t Int
  ext-var : Γ ⊆ Δ w/v X
          → Γ ⊆ Δ w/t ‶ X
  ext-arr : Γ ⊆ Ω w/t A
          → Ω ⊆ Δ w/t B
          → Γ ⊆ Δ w/t A `→ B
  ext-∀   : Γ ,∙ ⊆ Δ ,∙ w/t A
          → Γ ⊆ Δ w/t `∀ A
