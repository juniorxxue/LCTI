module Implicit.Algo.Find where

open import Implicit.Common
open import Implicit.Properties
open import Implicit.Algo

-- type variable k, appears in the type A
data bound : Env n m → Type m → Fin m → Set where
  b-var : ∀ {Γ : Env n m} {k}
    → bound Γ (‶ k) k
  b-arr₁ : ∀ {Γ : Env n m} {A B k}
    → bound Γ A k
    → bound Γ (A `→ B) k
  b-arr₂ : ∀ {Γ : Env n m} {A B k}
    → bound Γ B k
    → bound Γ (A `→ B) k
  b-∀ : ∀ {Γ : Env n m} {A k}
    → bound (Γ ,∙) A (#S k)
    → bound Γ (`∀ A) k

-- part of the type A, have the k type variable,
-- then the corresponding part in Σ must be e and e infers
data find : Env n m → Type m → Fin m → Context n m → Set where
  f-τ : ∀ {Γ : Env n m} {k A B}
    → (bd : bound Γ A k)
    → find Γ A k (τ B) -- not sure, maybe a B here
  f-arr-l : ∀ {Γ : Env n m} {A B k e Σ C}
    → (bd : bound Γ A k)
    → (⊢e : Γ ⊢ □ ⇒ e ⇒ C)
    → find Γ (A `→ B) k ([ e ]↝ Σ)
  f-arr-r : ∀ {Γ : Env n m} {A B k e Σ}
    → find Γ B k Σ
    → find Γ (A `→ B) k ([ e ]↝ Σ)
  f-∀ : ∀ {Σ : Context n m} {Γ A k}
    → find (Γ ,∙) A (#S k) (↑tyΣ0 Σ)
    → find Γ (`∀ A) k Σ

postulate
  s-find-gen : ∀ {Ψ Ψ' : SEnv n (1 + m)} {k Σ A B C}
    → k ^∈ Ψ
    → k := C ∈ Ψ'
    → Ψ ⊢ A ≤ Σ ⊣ Ψ' ↪ B
    → find (𝕄 Ψ') A k Σ

s-find : ∀ {Ψ Ψ' : SEnv n m} {Σ A B C}
  → Ψ ,^ ⊢ A ≤ Σ ⊣ Ψ' ,= B ↪ C
  → find (𝕄 Ψ' ,= B) A #0 Σ
s-find {B = B} s = s-find-gen {C = ↑ty0 B} Z (Z ↑ty-st⇘) s
