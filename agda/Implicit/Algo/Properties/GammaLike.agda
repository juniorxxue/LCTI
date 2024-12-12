module Implicit.Algo.Properties.GammaLike where

open import Implicit.Language
open import Implicit.Algo.Base
open import Implicit.Algo.Properties.Extension

private variable
  Ψ Ψ' : SEnv n m
  A B C : Type m
  Σ : Context n m

⊆Γ-like : ∀ {Ψ Ψ' : SEnv n m}
  → Γ-like Ψ
  → Ψ ⊆ Ψ'
  → Ψ ≡ Ψ'
⊆Γ-like gl base = refl 
⊆Γ-like (S∙ gl) (uvar ⊆Ψ) rewrite ⊆Γ-like gl ⊆Ψ = refl
⊆Γ-like (S, gl) (var ⊆Ψ) rewrite ⊆Γ-like gl ⊆Ψ = refl
⊆Γ-like (S= gl) (svar ⊆Ψ) rewrite ⊆Γ-like gl ⊆Ψ = refl

𝕎-Γ-like : ∀ (Γ : Env n m)
  → Γ-like (𝕎 Γ)
𝕎-Γ-like ∅ = Z
𝕎-Γ-like (Γ , A) = S, (𝕎-Γ-like Γ)
𝕎-Γ-like (Γ ,∙) = S∙ (𝕎-Γ-like Γ)
𝕎-Γ-like (Γ ,= A) = S= (𝕎-Γ-like Γ)
  
s-closed : ∀ {Ψ : SEnv n m} {Γ A B Σ}
  → 𝕎 Γ ⊢ A ≤⁺  Σ ⊣ Ψ ↪ B
  → Ψ ≡ 𝕎 Γ
s-closed {Γ = Γ} s with s⁺-⊆ s
... | r = sym (⊆Γ-like (𝕎-Γ-like Γ) r)


s-Γ-like : Ψ ⊢ A ≤⁺ Σ ⊣ Ψ' ↪ B
         → Γ-like Ψ
         → Γ-like Ψ'
