module Implicit.Algo.Properties.Environments where

open import Implicit.Language
open import Implicit.Algo.Base
open import Implicit.Algo.Properties.Extension
open import Implicit.Algo.Properties.OpenClose
open import Implicit.Algo.Properties.Polarity

-- we split Γ to be Γ₁ ++ Γ₂, in the k-th position
-- and free variables in A must appear in Γ₂

infix 3 _∤_⊢oˣ_
data _∤_⊢oˣ_ : Env n m → Fin m → Fin m → Set where

  opnx= : Γ ∋= X
        → Γ ∤ k ⊢oˣ X

  opnx∙ : Γ ∋∙ X
        → Γ ∤ k ⊢oˣ X

  opnx^ : Γ ∋^ X
        → X #< k
        → Γ ∤ k ⊢oˣ X

infix 3 _∤_⊢o_
data _∤_⊢o_ : Env n m → Fin m → Type m → Set where

  opn-int : Γ ∤ k ⊢o Int

  opn-var : Γ ∤ k ⊢oˣ X
          → Γ ∤ k ⊢o ‶ X

  opn-arr : Γ ∤ k ⊢o A
          → Γ ∤ k ⊢o B
          → Γ ∤ k ⊢o A `→ B

  opn-∀ : Γ ,∙ ∤ #S k ⊢o A
        → Γ ∤ k ⊢o `∀ A

infix 3 _⊆_∣_⊆_by_
data _⊆_∣_⊆_by_ : Env n m → Env n m → Env n m → Env n m → Fin m → Set where

  ⊆⊆-Z : (ext : Γ ⊆ Δ)
       → Γ ⊆ Δ ∣ Γ ⊆ Δ by #0
  ⊆⊆-S, : Γ₁ ⊆ Δ₁ ∣ Γ₂ ⊆ Δ₂ by k
        → Γ₁ , A ⊆ Δ₁ , A ∣ Γ₂ , A ⊆ Δ₂ , A by k
  ⊆-S^^  : Γ₁ ⊆ Δ₁ ∣ Γ₂ ⊆ Δ₂ by k
        → Γ₁ ,^ ⊆ Δ₁ ,^ ∣ Γ₂ ,^ ⊆ Δ₂ ,^ by #S k
  ⊆-S∙∙  : Γ₁ ⊆ Δ₁ ∣ Γ₂ ⊆ Δ₂ by k
        → Γ₁ ,∙ ⊆ Δ₁ ,∙ ∣ Γ₂ ,∙ ⊆ Δ₂ ,∙ by #S k
  ⊆-S==  : Γ₁ ⊆ Δ₁ ∣ Γ₂ ⊆ Δ₂ by k
         → Γ₁ ,= A ⊆ Δ₁ ,= A ∣ Γ₂ ,= A ⊆ Δ₂ ,= A by #S k
  ⊆-S^=  : Γ₁ ⊆ Δ₁ ∣ Γ₂ ⊆ Δ₂ by k
         → Γ₁ ,^ ⊆ Δ₁ ,^ ∣ Γ₂ ,= A ⊆ Δ₂ ,= A by #S k


⊆⊆-one-input : Γ₁ ⊆ Δ₁ ∣ Γ₁ ⊆ Δ₂ by k
             → Δ₁ ≡ Δ₂
⊆⊆-one-input (⊆⊆-Z ext) = refl
⊆⊆-one-input (⊆⊆-S, exts) rewrite ⊆⊆-one-input exts = refl
⊆⊆-one-input (⊆-S^^ exts) rewrite ⊆⊆-one-input exts = refl
⊆⊆-one-input (⊆-S∙∙ exts) rewrite ⊆⊆-one-input exts = refl
⊆⊆-one-input (⊆-S== exts) rewrite ⊆⊆-one-input exts = refl

⊆⊆-⊆-l : Γ₁ ⊆ Δ₁ ∣ Γ₂ ⊆ Δ₂ by k
       → Γ₁ ⊆ Δ₁
⊆⊆-⊆-l (⊆⊆-Z ext) = ext
⊆⊆-⊆-l (⊆⊆-S, exts) = var (⊆⊆-⊆-l exts)
⊆⊆-⊆-l (⊆-S^^ exts) = evar (⊆⊆-⊆-l exts)
⊆⊆-⊆-l (⊆-S∙∙ exts) = uvar (⊆⊆-⊆-l exts)
⊆⊆-⊆-l (⊆-S== exts) = svar (⊆⊆-⊆-l exts)
⊆⊆-⊆-l (⊆-S^= exts) = evar (⊆⊆-⊆-l exts)

⊆⊆-⊆-r : Γ₁ ⊆ Δ₁ ∣ Γ₂ ⊆ Δ₂ by k
       → Γ₂ ⊆ Δ₂
⊆⊆-⊆-r (⊆⊆-Z ext) = ext
⊆⊆-⊆-r (⊆⊆-S, exts) = var (⊆⊆-⊆-r exts)
⊆⊆-⊆-r (⊆-S^^ exts) = evar (⊆⊆-⊆-r exts)
⊆⊆-⊆-r (⊆-S∙∙ exts) = uvar (⊆⊆-⊆-r exts)
⊆⊆-⊆-r (⊆-S== exts) = svar (⊆⊆-⊆-r exts)
⊆⊆-⊆-r (⊆-S^= exts) = svar (⊆⊆-⊆-r exts)


⊆⊆-open-var-in : Γ₁ ∋^ X
               → X #< k
               → Γ₁ ⊆ Δ₁ ∣ Γ₂ ⊆ Δ₂ by k
               → Δ₁ ∋^ X
⊆⊆-open-var-in Z lt (⊆-S^^ exts) = Z
⊆⊆-open-var-in Z lt (⊆-S^= exts) = Z
⊆⊆-open-var-in (S, inΓ) lt (⊆⊆-S, exts) = S, (⊆⊆-open-var-in inΓ lt exts)
⊆⊆-open-var-in (S∙ inΓ) (s≤s lt) (⊆-S∙∙ exts) = S∙ (⊆⊆-open-var-in inΓ lt exts)
⊆⊆-open-var-in (S= inΓ) (s≤s lt) (⊆-S== exts) = S= (⊆⊆-open-var-in inΓ lt exts)
⊆⊆-open-var-in (S^ inΓ) (s≤s lt) (⊆-S^^ exts) = S^ (⊆⊆-open-var-in inΓ lt exts)
⊆⊆-open-var-in (S^ inΓ) (s≤s lt) (⊆-S^= exts) = S^ (⊆⊆-open-var-in inΓ lt exts)


⊆⊆-open-var : Γ₁ ∋^ X
            → Γ₁ ∤ k ⊢oˣ X
            → Γ₁ ⊆ Δ₁ ∣ Γ₂ ⊆ Δ₂ by k
            → Δ₁ ∋^ X
⊆⊆-open-var inΓ (opnx= x) exts = ⊥-elim (^∈-=∈-false inΓ x)
⊆⊆-open-var inΓ (opnx∙ x) exts = ⊥-elim (^∈-∙∈-false inΓ x)
⊆⊆-open-var inΓ (opnx^ x x₁) exts = ⊆⊆-open-var-in inΓ x₁ exts
