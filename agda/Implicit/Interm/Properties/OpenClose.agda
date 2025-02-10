module Implicit.Interm.Properties.OpenClose where

open import Implicit.Language.All
open import Implicit.Interm.Base

----------------------------------------------------------------------
--+                           subtyping                            +--
----------------------------------------------------------------------

s-closed : Γ ⊢ j # A ≤ B
       → Closed Γ
s-closed (s-refl cloΣ cloA) = cloΣ
s-closed (s-int cloΓ) = cloΓ
s-closed (s-var-∙ cloΓ inΓ) = cloΓ
s-closed (s-var-= cloΓ inΓ) = cloΓ
s-closed (s-arr₁ s s₁) = s-closed s
s-closed (s-arr₂ s s₁) = s-closed s
s-closed (s-arr₃ cloA s) = s-closed s
s-closed (s-∀ s) with s-closed s
... | clo-S∙ r = r
s-closed (s-∀l s ic fd st₁ st₂) with s-closed s
... | clo-S= r cloA = r
s-closed (s-var-l x s) = s-closed s
s-closed (s-var-r x s) = s-closed s

s-close-l : Γ ⊢ j # A ≤ B
       → Γ ⊢c A
s-close-r : Γ ⊢ j # A ≤ B
       → Γ ⊢c B

s-close-l (s-refl cloΣ cloA) = cloA
s-close-l (s-int cloΓ) = ⊢c-int
s-close-l (s-var-∙ cloΓ inΓ) = ⊢c-var-∙ inΓ
s-close-l (s-var-= cloΓ inΓ) = ⊢c-var-= inΓ
s-close-l (s-arr₁ s s₁) = ⊢c-arr (s-close-r s) (s-close-l s₁)
s-close-l (s-arr₂ s s₁) = ⊢c-arr (s-close-r s) (s-close-l s₁)
s-close-l (s-arr₃ cloA s) = ⊢c-arr cloA (s-close-l s)
s-close-l (s-∀ s) = ⊢c-∀ (s-close-l s)
s-close-l (s-∀l s ic fd st₁ st₂) = ⊢c-∀ (⊢c-◆0 (s-close-l s))
s-close-l (s-var-l x s) = ⊢c-var-= (∋:=to∋= x)
s-close-l (s-var-r x s) = s-close-l s

s-close-r (s-refl cloΣ cloA) = cloA
s-close-r (s-int cloΓ) = ⊢c-int
s-close-r (s-var-∙ cloΓ inΓ) = ⊢c-var-∙ inΓ
s-close-r (s-var-= cloΓ inΓ) = ⊢c-var-= inΓ
s-close-r (s-arr₁ s s₁) = ⊢c-arr (s-close-l s) (s-close-r s₁)
s-close-r (s-arr₂ s s₁) = ⊢c-arr (s-close-l s) (s-close-r s₁)
s-close-r (s-arr₃ cloA s) = ⊢c-arr cloA (s-close-r s)
s-close-r (s-∀ s) = ⊢c-∀ (s-close-r s)
s-close-r (s-∀l s ic fd st₁ st₂) with s-closed s
... | clo-S= r cloA = ⊢c-subst0 (s-close-r s) cloA (st-arr st₁ st₂)
s-close-r (s-var-l x s) = s-close-r s
s-close-r (s-var-r x s) = ⊢c-var-= (∋:=to∋= x)

----------------------------------------------------------------------
--+                             typing                             +--
----------------------------------------------------------------------

t-closed : Γ ⊢ j # e ⦂ A
       → Closed Γ
t-closed (⊢lit cloΣ) = cloΣ
t-closed (⊢var cloΣ x∈Γ) = cloΣ
t-closed (⊢ann ⊢e) = t-closed ⊢e
t-closed (⊢lam₁ ⊢e) with t-closed ⊢e
... | clo-S, r cloA = r
t-closed (⊢lam₂ ⊢e) with t-closed ⊢e
... | clo-S, r cloA = r
t-closed (⊢app₁ ⊢e ⊢e₁) = t-closed ⊢e
t-closed (⊢app₂ ⊢e ⊢e₁) = t-closed ⊢e
t-closed (⊢sub ⊢e B≤A j≢Z) = t-closed ⊢e
t-closed (⊢tabs ⊢e) with t-closed ⊢e
... | clo-S∙ r = r

t-close : Γ ⊢ j # e ⦂ A
       → Γ ⊢c A
t-close (⊢lit cloΣ) = ⊢c-int
t-close (⊢var cloΣ x∈Γ) = ∋⦂-closed cloΣ x∈Γ
t-close (⊢ann ⊢e) = t-close ⊢e
t-close (⊢lam₁ ⊢e) with t-closed ⊢e
... | clo-S, r cloA = ⊢c-arr cloA (⊢c-strengthen,0 (t-close ⊢e))
t-close (⊢lam₂ ⊢e) with t-closed ⊢e
... | clo-S, r cloA = ⊢c-arr cloA (⊢c-strengthen,0 (t-close ⊢e))
t-close (⊢app₁ ⊢e ⊢e₁) with t-close ⊢e
... | ⊢c-arr r r₁ = r₁
t-close (⊢app₂ ⊢e ⊢e₁) with t-close ⊢e
... | ⊢c-arr r r₁ = r₁
t-close (⊢sub ⊢e B≤A j≢Z) = s-close-r B≤A
t-close (⊢tabs ⊢e) = ⊢c-∀ (t-close ⊢e)
