module Implicit.Algo.Properties.Find where

open import Implicit.Language
open import Implicit.Algo.Base

-- part of the type A, have the k type variable,
-- then the corresponding part in Σ must be e and e infers
data find : Env n m → Type m → Fin m → Context n m → Set where
  f-τ : ∀ {Γ : Env n m} {k A B}
    → (bd : k ε A)
    → find Γ A k (τ B) -- not sure, maybe a B here
  f-arr-l : ∀ {Γ : Env n m} {A B k e Σ C}
    → (bd : k ε A)
    → (⊢e : Γ ⊢ □ ⇒ e ⇒ C)
    → find Γ (A `→ B) k ([ e ]↝ Σ)
  f-arr-r : ∀ {Γ : Env n m} {A B k e Σ}
    → find Γ B k Σ
    → find Γ (A `→ B) k ([ e ]↝ Σ)
  f-∀ : ∀ {Σ : Context n m} {Σ' Γ A k}
    → find (Γ ,∙) A (#S k) Σ'
    → ↑tyᶜ0 Σ ⇘ Σ'
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
s-find {B = B} s = s-find-gen Z (Z (proj₂ (↑ty0-total B))) s
