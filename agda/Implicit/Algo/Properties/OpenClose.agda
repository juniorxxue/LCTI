module Implicit.Algo.Properties.OpenClose where

open import Implicit.Language
open import Implicit.Algo.Base

private variable
  Ψ : SEnv n m
  A : Type m

postulate
  ⊢a→⊢c : ∀ {Γ : Env n m} {Σ e A}
    → Γ ⊢ Σ ⇒ e ⇒ A
    → 𝕎 Γ ⊢c A

  ⊢a→⊢c-τ : ∀ {Γ : Env n m} {e A B}
    → Γ ⊢ τ B ⇒ e ⇒ A
    → 𝕎 Γ ⊢c B

  ⊢a→⊢c-weaken : ∀ {Γ : Env n m} {Σ e A B}
    → Γ , B ⊢ Σ ⇒ e ⇒ A
    → 𝕎 Γ ⊢c A

  s-closed-r : ∀ {Ψ : SEnv n m} {Γ A B Σ}
    → 𝕎 Γ ⊢ A ≤ Σ ⊣ Ψ ↪ B
    → 𝕎 Γ ⊢ A ≤ Σ ⊣ 𝕎 Γ ↪ B

  s-closed-l : ∀ {Ψ : SEnv n m} {Γ A B Σ}
    → Ψ ⊢ A ≤ Σ ⊣ 𝕎 Γ ↪ B
    → 𝕎 Γ ⊢ A ≤ Σ ⊣ 𝕎 Γ ↪ B

  ⊢c-⊢o-⊥ : Ψ ⊢c A → Ψ ⊢o A → ⊥
    
