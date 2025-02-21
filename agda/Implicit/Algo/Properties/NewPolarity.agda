module Implicit.Algo.Properties.NewPolarity where

open import Implicit.Language.All
open import Implicit.Algo.Base
open import Implicit.Algo.Properties.NewExtension

postulate
  ⊆-∋∙' : Δ ∋∙ k
        → Γ ⊆ Δ
        → Γ ∋∙ k

⊆-∋=¹' : Δ ∋=¹ k
        → Γ ⊆ Δ
        → Γ ∋=¹ k
⊆-∋=¹' (S, inΔ) (var ext) = S, (⊆-∋=¹' inΔ ext)
⊆-∋=¹' (S∙ inΔ) (uvar ext) = S∙ (⊆-∋=¹' inΔ ext)
⊆-∋=¹' (S^ inΔ) (evar ext) = S^ (⊆-∋=¹' inΔ ext)
⊆-∋=¹' (S= inΔ) (evar-sol ext x cloA) = S^ (⊆-∋=¹' inΔ ext)
⊆-∋=¹' (S= inΔ) (svar ext) = S= (⊆-∋=¹' inΔ ext)
⊆-∋=¹' (S⋈ x) (mark ext) = S⋈ {!!}

-- ⊆-⊢c¹ : Δ ⊢c¹ A
--       → Γ ⊆ Δ
--       → Γ ⊢c¹ A
-- ⊆-⊢c¹ ⊢c¹-int ext = ⊢c¹-int
-- ⊆-⊢c¹ (⊢c¹-var-∙ inΓ) ext = ⊢c¹-var-∙ (⊆-∋∙' inΓ ext)
-- ⊆-⊢c¹ (⊢c¹-var-= inΓ) ext = ⊢c¹-var-= (⊆-∋=¹' inΓ ext)
-- ⊆-⊢c¹ (⊢c¹-arr cloA cloA₁) ext = ⊢c¹-arr (⊆-⊢c¹ cloA ext) (⊆-⊢c¹ cloA₁ ext)
-- ⊆-⊢c¹ (⊢c¹-∀ cloA) ext = ⊢c¹-∀ (⊆-⊢c¹ cloA (uvar ext))

-- data Polarity (Γ : Env n m) (A : Type m) (Σ : Context n m) : Polar → Set where
--   polar-l : (cloA : Γ ⊢c¹ A) → Polarity Γ A Σ ≤⁻
--   polar-r : (cloΣ : Γ ⊢cᶜ¹ Σ) → Polarity Γ A Σ ≤⁺

-- s-polarity : Γ ⊢ A ⌞ ≤ ⌝ Σ ⊣ Δ ↪ B
--            → Polarity Γ A Σ ≤
-- s-polarity {≤ = ≤⁺} (s-int cloΓ) = polar-r (⊢c-τ ⊢c¹-int)
-- s-polarity {≤ = ≤⁻} (s-int cloΓ) = polar-l ⊢c¹-int
-- s-polarity (s-empty cloΓ clo) = polar-r ⊢c-empty
-- s-polarity {≤ = ≤⁺} (s-var-∙ cloΓ x) = polar-r (⊢c-τ (⊢c¹-var-∙ x))
-- s-polarity {≤ = ≤⁻} (s-var-∙ cloΓ x) = polar-l (⊢c¹-var-∙ x)
-- s-polarity {≤ = ≤⁺} (s-var-= cloΓ x) = polar-r (⊢c-τ (⊢c¹-var-= x))
-- s-polarity {≤ = ≤⁻} (s-var-= cloΓ x) = polar-l (⊢c¹-var-= x)
-- s-polarity (s-ex-l^ x-in cloA inst) = polar-r (⊢c-τ cloA)
-- s-polarity (s-ex-l= x-in s) with s-polarity s
-- ... | polar-r (⊢c-τ cloA) = polar-r (⊢c-τ cloA)
-- s-polarity {≤ = ≤⁺} (s-ex-typ-l= x-in s) with s-polarity s
-- ... | polar-r (⊢c-τ cloA) = polar-r (⊢c-τ cloA)
-- s-polarity {≤ = ≤⁻} (s-ex-typ-l= x-in s) with s-polarity s
-- ... | polar-l cloA = polar-l (⊢c¹-var-= (∋:=¹-∋= x-in))
-- s-polarity (s-ex-r^ x-in cloA inst) = polar-l cloA
-- s-polarity (s-ex-r= x-in s) with s-polarity s
-- ... | polar-l cloA = polar-l cloA
-- s-polarity (s-ex-typ-r= x-in s) with s-polarity s
-- ... | polar-l cloA = polar-l cloA
-- ... | polar-r (⊢c-τ cloA) = polar-r (⊢c-τ (⊢c¹-var-= (∋:=¹-∋= x-in)))
-- s-polarity {≤ = ≤⁺} (s-arr s s₁) with s-polarity s | s-polarity s₁
-- ... | polar-l cloA | polar-r (⊢c-τ cloA₁) = polar-r (⊢c-τ (⊢c¹-arr cloA {!!}))
-- s-polarity {≤ = ≤⁻} (s-arr s s₁) with s-polarity s | s-polarity s₁
-- ... | polar-r (⊢c-τ cloA₁) | polar-l cloA = polar-l (⊢c¹-arr cloA₁ {!!})
-- s-polarity (s-term-c ⊢e s) = polar-r (⊢c-term {!!})
-- s-polarity (s-term-o opnA ⊢e s s₁) with s-polarity s₁
-- ... | polar-r cloΣ = polar-r (⊢c-term {!!})
-- s-polarity (s-∀ s) with s-polarity s
-- ... | polar-l cloA = polar-l (⊢c¹-∀ cloA)
-- ... | polar-r (⊢c-τ cloA) = polar-r (⊢c-τ (⊢c¹-∀ cloA))
-- s-polarity (s-∀l s upᶜ upᵉ st₁ st₂) with s-polarity s
-- ... | polar-r (⊢c-term cloΣ) = polar-r (⊢c-term {!!})
