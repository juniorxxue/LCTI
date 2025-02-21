module Implicit.Interm.Properties.Polarity where

open import Implicit.Language.All
open import Implicit.Interm.Base

-- polarity should consider two factors to force closeness
-- 1. counter, to indicate what parts
-- 2. polar, to indicate left or right

infix 3 _⊢c¹_w/c_
data _⊢c¹_w/c_ : Env n m → Type m → Counter → Set where
  cc-∞ : Γ ⊢c¹ A
       → Γ ⊢c¹ A w/c ∞
  cc-0 : Γ ⊢c¹ A w/c Z
  cc-𝕚 : Γ ⊢c¹ B w/c j
       → Γ ⊢c¹ A `→ B w/c 𝕚 j -- a bit pause, since algo doesn't restrict this
  cc-𝕔 : Γ ⊢c¹ B w/c j
       → Γ ⊢c¹ A `→ B w/c 𝕔 j

postulate
  ⊢c¹w/c-subst0 : Γ ,= B ⊢c¹ C `→ D w/c j
               → ⟦ B ⟧ D ⇘ D*
               → ⟦ B ⟧ C ⇘ C*
               → Γ ⊢c¹ C* `→ D* w/c j



data Polarity (Γ : Env n m) (j : Counter) (A : Type m) (B : Type m) : Polar → Set where
  pr-l : Γ ⊢c¹ A
       → Polarity Γ j A B ≤⁻
  pr-r : Γ ⊢c¹ B w/c j
       → Polarity Γ j A B ≤⁺


s-polarity : Γ ⊢ j # A ⌞ ≤ ⌝ B
           → Polarity Γ j A B ≤
s-polarity (s-refl cloΓ cloA) = pr-r cc-0
s-polarity {≤ = ≤⁺} (s-int cloΓ) = pr-r (cc-∞ ⊢c¹-int)
s-polarity {≤ = ≤⁻} (s-int cloΓ) = pr-l ⊢c¹-int
s-polarity {≤ = ≤⁺} (s-var-∙ cloΓ inΓ) = pr-r (cc-∞ (⊢c¹-var-∙ inΓ))
s-polarity {≤ = ≤⁻} (s-var-∙ cloΓ inΓ) = pr-l (⊢c¹-var-∙ inΓ)
s-polarity {≤ = ≤⁺} (s-var-= cloΓ inΓ) = pr-r (cc-∞ (⊢c¹-var-= inΓ))
s-polarity {≤ = ≤⁻} (s-var-= cloΓ inΓ) = pr-l (⊢c¹-var-= inΓ)
s-polarity {≤ = ≤⁺} (s-arr₁ s s₁) with s-polarity s | s-polarity s₁
... | pr-l x | pr-r (cc-∞ x₁) = pr-r (cc-∞ (⊢c¹-arr x x₁))
s-polarity {≤ = ≤⁻} (s-arr₁ s s₁) with s-polarity s | s-polarity s₁
... | pr-r (cc-∞ x) | pr-l x₁ = pr-l (⊢c¹-arr x x₁)
s-polarity (s-arr₂ s s₁) with s-polarity s | s-polarity s₁
... | pr-l x | pr-r x₁ = pr-r (cc-𝕚 x₁)
s-polarity (s-arr₃ cloA s) with s-polarity s
... | pr-r x = pr-r (cc-𝕔 x)
s-polarity (s-∀ s) with s-polarity s
... | pr-l x = pr-l (⊢c¹-∀ x)
... | pr-r (cc-∞ x) = pr-r (cc-∞ (⊢c¹-∀ x))
s-polarity (s-∀l s ic fd stC stD) with s-polarity s
... | pr-r x = pr-r (⊢c¹w/c-subst0 x stD stC)
s-polarity (s-var-sub-l inΓ s) with s-polarity s
... | pr-r x = pr-r x
s-polarity (s-var-sub-r inΓ s) with s-polarity s
... | pr-l x = pr-l x
s-polarity (s-var-typ-l inΓ s) with s-polarity s
... | pr-l x = pr-l (⊢c¹-var-= (∋:=¹-∋= inΓ))
... | pr-r (cc-∞ x) = pr-r (cc-∞ x)
s-polarity (s-var-typ-r inΓ s) with s-polarity s
... | pr-l x = pr-l x
... | pr-r (cc-∞ x) = pr-r (cc-∞ (⊢c¹-var-= (∋:=¹-∋= inΓ)))
