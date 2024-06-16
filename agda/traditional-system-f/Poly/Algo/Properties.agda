module Poly.Algo.Properties where

open import Poly.Common
open import Poly.Algo
  
s-closed : ∀ {Γ Γ' : Env n m} {A B Σ}
  → Γ ⊢ A ≤ Σ ⊣ Γ' ↪ B
  → Γ ≡ Γ'
s-closed s-int = refl
s-closed s-empty = refl
s-closed s-var = refl
s-closed (s-ex-l= x s) = s-closed s
s-closed (s-ex-r= x s) = s-closed s
s-closed (s-arr s s₁) rewrite s-closed s | s-closed s₁ = refl
s-closed (s-term-c x s) = s-closed s
s-closed (s-∀ s) with s-closed s
... | refl = refl
s-closed (s-∀-t s) with s-closed s
... | refl = refl
