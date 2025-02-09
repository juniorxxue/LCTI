module Implicit.Interm.Properties.Strengthen where

open import Implicit.Language.All
open import Implicit.Interm.Base

s-strengthen, : Γ ⊢ j # A ≤ B
              → Γ ◀ k ,⇘ Γ'
              → Γ' ⊢ j # A ≤ B
s-strengthen, (s-refl cloΓ cloA) newΓ = s-refl (closed-strengthen, cloΓ newΓ) (⊢c-strengthen, cloA newΓ)
s-strengthen, (s-int cloΓ) newΓ = s-int (closed-strengthen, cloΓ newΓ)
s-strengthen, (s-var-∙ cloΓ inΓ) newΓ = s-var-∙ (closed-strengthen, cloΓ newΓ) (◀,-∋∙ inΓ newΓ)
s-strengthen, (s-var-= cloΓ inΓ) newΓ = s-var-= (closed-strengthen, cloΓ newΓ) (◀,-∋= inΓ newΓ)
s-strengthen, (s-arr₁ s s₁) newΓ = s-arr₁ (s-strengthen, s newΓ) (s-strengthen, s₁ newΓ)
s-strengthen, (s-arr₂ s s₁) newΓ = s-arr₂ (s-strengthen, s newΓ) (s-strengthen, s₁ newΓ)
s-strengthen, (s-arr₃ cloA s) newΓ = s-arr₃ (⊢c-strengthen, cloA newΓ) (s-strengthen, s newΓ)
s-strengthen, (s-∀ s) newΓ = s-∀ (s-strengthen, s (◀S∙ newΓ))
s-strengthen, (s-∀l s ic fd st₁ st₂) newΓ = s-∀l (s-strengthen, s (◀S= newΓ)) ic fd st₁ st₂
s-strengthen, (s-var-l inΓ s) newΓ = s-var-l (◀,-∋:= inΓ newΓ) (s-strengthen, s newΓ)
s-strengthen, (s-var-r inΓ s) newΓ = s-var-r (◀,-∋:= inΓ newΓ) (s-strengthen, s newΓ)

t-strengthen, : Γ ⊢ j # e' ⦂ A
              → Γ ◀ k ,⇘ Γ'
              → e ↑tm k ⇘ e'
              → Γ' ⊢ j # e ⦂ A
t-strengthen, (⊢lit cloΣ) newΓ ↑tm-lit = ⊢lit (closed-strengthen, cloΣ newΓ)
t-strengthen, (⊢var cloΣ x∈Γ) newΓ ↑tm-var = ⊢var (closed-strengthen, cloΣ newΓ) (◀,-∋⦂ x∈Γ newΓ)
t-strengthen, (⊢ann ⊢e) newΓ (↑tm-⦂ up-e) = ⊢ann (t-strengthen, ⊢e newΓ up-e)
t-strengthen, (⊢lam₁ ⊢e) newΓ (↑tm-ƛ up-e) = ⊢lam₁ (t-strengthen, ⊢e (◀S, newΓ) up-e)
t-strengthen, (⊢lam₂ ⊢e) newΓ (↑tm-ƛ up-e) = ⊢lam₂ (t-strengthen, ⊢e (◀S, newΓ) up-e)
t-strengthen, (⊢app₁ ⊢e ⊢e₁) newΓ (↑tm-app up-e up-e₁) = ⊢app₁ (t-strengthen, ⊢e newΓ up-e) (t-strengthen, ⊢e₁ newΓ up-e₁)
t-strengthen, (⊢app₂ ⊢e ⊢e₁) newΓ (↑tm-app up-e up-e₁) = ⊢app₂ (t-strengthen, ⊢e newΓ up-e) (t-strengthen, ⊢e₁ newΓ up-e₁)
t-strengthen, (⊢sub ⊢e B≤A j≢Z) newΓ up-e = ⊢sub (t-strengthen, ⊢e newΓ up-e) (s-strengthen, B≤A newΓ) j≢Z
t-strengthen, (⊢tabs ⊢e) newΓ (↑tm-Λ up-e) = ⊢tabs (t-strengthen, ⊢e (◀S∙ newΓ) up-e)


t-strengthen,0 : Γ , T ⊢ j # e' ⦂ A
               → ↑tm0 e ⇘ e'
               → Γ ⊢ j # e ⦂ A
t-strengthen,0 ⊢e up = t-strengthen, ⊢e ◀Z up
