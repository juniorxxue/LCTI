module Implicit.Interm.Properties.OpenClose where

open import Implicit.Language.All
open import Implicit.Interm.Base

----------------------------------------------------------------------
--+                           subtyping                            +--
----------------------------------------------------------------------

s-cloΓ : Γ ⊢ j # A ≤ B
       → Closed Γ
s-cloΓ (s-refl cloΣ cloA) = cloΣ
s-cloΓ (s-int cloΓ) = cloΓ
s-cloΓ (s-var-∙ cloΓ inΓ) = cloΓ
s-cloΓ (s-var-= cloΓ inΓ) = cloΓ
s-cloΓ (s-arr₁ s s₁) = s-cloΓ s
s-cloΓ (s-arr₂ s s₁) = s-cloΓ s
s-cloΓ (s-arr₃ cloA s) = s-cloΓ s
s-cloΓ (s-∀ s) with s-cloΓ s
... | clo-S∙ r = r
s-cloΓ (s-∀l s ic fd st₁ st₂) with s-cloΓ s
... | clo-S= r cloA = r
s-cloΓ (s-var-l x s) = s-cloΓ s
s-cloΓ (s-var-r x s) = s-cloΓ s

s-cloA : Γ ⊢ j # A ≤ B
       → Γ ⊢c A
s-cloB : Γ ⊢ j # A ≤ B
       → Γ ⊢c B

s-cloA (s-refl cloΣ cloA) = cloA
s-cloA (s-int cloΓ) = ⊢c-int
s-cloA (s-var-∙ cloΓ inΓ) = ⊢c-var-∙ inΓ
s-cloA (s-var-= cloΓ inΓ) = ⊢c-var-= inΓ
s-cloA (s-arr₁ s s₁) = ⊢c-arr (s-cloB s) (s-cloA s₁)
s-cloA (s-arr₂ s s₁) = ⊢c-arr (s-cloB s) (s-cloA s₁)
s-cloA (s-arr₃ cloA s) = ⊢c-arr cloA (s-cloA s)
s-cloA (s-∀ s) = ⊢c-∀ (s-cloA s)
s-cloA (s-∀l s ic fd st₁ st₂) = ⊢c-∀ (⊢c-◆0 (s-cloA s))
s-cloA (s-var-l x s) = ⊢c-var-= (:=to= x)
s-cloA (s-var-r x s) = s-cloA s

s-cloB (s-refl cloΣ cloA) = cloA
s-cloB (s-int cloΓ) = ⊢c-int
s-cloB (s-var-∙ cloΓ inΓ) = ⊢c-var-∙ inΓ
s-cloB (s-var-= cloΓ inΓ) = ⊢c-var-= inΓ
s-cloB (s-arr₁ s s₁) = ⊢c-arr (s-cloA s) (s-cloB s₁)
s-cloB (s-arr₂ s s₁) = ⊢c-arr (s-cloA s) (s-cloB s₁)
s-cloB (s-arr₃ cloA s) = ⊢c-arr cloA (s-cloB s)
s-cloB (s-∀ s) = ⊢c-∀ (s-cloB s)
s-cloB (s-∀l s ic fd st₁ st₂) with s-cloΓ s
... | clo-S= r cloA = ⊢c-subst0 (s-cloB s) cloA (st-arr st₁ st₂)
s-cloB (s-var-l x s) = s-cloB s
s-cloB (s-var-r x s) = ⊢c-var-= (:=to= x)

----------------------------------------------------------------------
--+                             typing                             +--
----------------------------------------------------------------------

t-cloΓ : Γ ⊢ j # e ⦂ A
       → Closed Γ
t-cloΓ (⊢lit cloΣ) = cloΣ
t-cloΓ (⊢var cloΣ x∈Γ) = cloΣ
t-cloΓ (⊢ann ⊢e) = t-cloΓ ⊢e
t-cloΓ (⊢lam₁ ⊢e) with t-cloΓ ⊢e
... | clo-S, r cloA = r
t-cloΓ (⊢lam₂ ⊢e) with t-cloΓ ⊢e
... | clo-S, r cloA = r
t-cloΓ (⊢app₁ ⊢e ⊢e₁) = t-cloΓ ⊢e
t-cloΓ (⊢app₂ ⊢e ⊢e₁) = t-cloΓ ⊢e
t-cloΓ (⊢sub ⊢e B≤A j≢Z) = t-cloΓ ⊢e
t-cloΓ (⊢tabs ⊢e) with t-cloΓ ⊢e
... | clo-S∙ r = r

t-cloA : Γ ⊢ j # e ⦂ A
       → Γ ⊢c A
t-cloA (⊢lit cloΣ) = ⊢c-int
t-cloA (⊢var cloΣ x∈Γ) = ∋⦂-closed cloΣ x∈Γ
t-cloA (⊢ann ⊢e) = t-cloA ⊢e
t-cloA (⊢lam₁ ⊢e) with t-cloΓ ⊢e
... | clo-S, r cloA = ⊢c-arr cloA (⊢c-strengthen,0 (t-cloA ⊢e))
t-cloA (⊢lam₂ ⊢e) with t-cloΓ ⊢e
... | clo-S, r cloA = ⊢c-arr cloA (⊢c-strengthen,0 (t-cloA ⊢e))
t-cloA (⊢app₁ ⊢e ⊢e₁) with t-cloA ⊢e
... | ⊢c-arr r r₁ = r₁
t-cloA (⊢app₂ ⊢e ⊢e₁) with t-cloA ⊢e
... | ⊢c-arr r r₁ = r₁
t-cloA (⊢sub ⊢e B≤A j≢Z) = s-cloB B≤A
t-cloA (⊢tabs ⊢e) = ⊢c-∀ (t-cloA ⊢e)
