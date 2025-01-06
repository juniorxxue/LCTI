module Implicit.Language.OpenClose.Subst where

open import Implicit.Language.Base
open import Implicit.Language.Lookup
open import Implicit.Language.Shift
open import Implicit.Language.Subst
open import Implicit.Language.OpenClose.Base

◀=-imply-∋= : Γ ◀ k := T ⇘ Γ*
            → Γ ∋= k
◀=-imply-∋= ◀Z = Z
◀=-imply-∋= (◀S, newΓ x) = S, (◀=-imply-∋= newΓ)
◀=-imply-∋= (◀S^ newΓ x) = S^ (◀=-imply-∋= newΓ)
◀=-imply-∋= (◀S∙ newΓ x) = S∙ (◀=-imply-∋= newΓ)
◀=-imply-∋= (◀S= newΓ x x₁) = S= (◀=-imply-∋= newΓ)

◀=-neq-∋∙ : ∀ {Γ : Env n (1 + m)}
          → Γ ∋∙ X
          → Γ ◀ k := T ⇘ Γ*
          → (¬p : k ≢ X)
          → Γ* ∋∙ punchOut ¬p
◀=-neq-∋∙ {m = m} {X = #0} {k = #0} inΓ newΓ ¬p = ⊥-elim (¬p refl)
◀=-neq-∋∙ {m = suc m} {X = #0} {k = #S k} (S, inΓ) (◀S, newΓ x) ¬p = S, (◀=-neq-∋∙ inΓ newΓ ¬p)
◀=-neq-∋∙ {m = suc m} {X = #0} {k = #S k} inΓ (◀S∙ newΓ x) ¬p = Z
◀=-neq-∋∙ {m = suc m} {X = #S X} {k = #0} (S, inΓ) (◀S, newΓ x) ¬p = S, (◀=-neq-∋∙ inΓ newΓ ¬p)
◀=-neq-∋∙ {m = suc m} {X = #S X} {k = #0} (S= inΓ) ◀Z ¬p = inΓ
◀=-neq-∋∙ {m = suc m} {X = #S X} {k = #S k} (S, inΓ) (◀S, newΓ x) ¬p = S, (◀=-neq-∋∙ inΓ newΓ ¬p)
◀=-neq-∋∙ {m = suc m} {X = #S X} {k = #S k} (S^ inΓ) (◀S^ newΓ x) ¬p = S^ (◀=-neq-∋∙ inΓ newΓ (≢-pred ¬p))
◀=-neq-∋∙ {m = suc m} {X = #S X} {k = #S k} (S∙ inΓ) (◀S∙ newΓ x) ¬p = S∙ (◀=-neq-∋∙ inΓ newΓ (≢-pred ¬p))
◀=-neq-∋∙ {m = suc m} {X = #S X} {k = #S k} (S= inΓ) (◀S= newΓ x x₁) ¬p = S= (◀=-neq-∋∙ inΓ newΓ (≢-pred ¬p))

⊢c-subst : Γ ⊢c A
         → Γ ◀ k := T ⇘ Γ*
         → T ↑ty k ⇘ T'
         → Γ ⊢c T'
         → ⟦ k / T ⟧ A ⇘ A*
         → Γ* ⊢c A*
⊢c-subst ⊢c-int newΓ upT cloT st-int = ⊢c-int
⊢c-subst (⊢c-var-∙ inΓ) newΓ upT cloT (st-var stx-eq) = ⊥-elim (∙∈-=∈-false inΓ (◀=-imply-∋= newΓ))
⊢c-subst (⊢c-var-∙ inΓ) newΓ upT cloT (st-var (stx-neq ¬p)) = ⊢c-var-∙ (◀=-neq-∋∙ inΓ newΓ ¬p)
⊢c-subst (⊢c-var-= inΓ) newΓ upT cloT (st-var stx-eq) = {!!}
⊢c-subst (⊢c-var-= inΓ) newΓ upT cloT (st-var (stx-neq ¬p)) = {!!}
⊢c-subst (⊢c-arr cloA cloA₁) newΓ upT cloT (st-arr stA stA₁) = ⊢c-arr (⊢c-subst cloA newΓ upT cloT stA) (⊢c-subst cloA₁ newΓ upT cloT stA₁)
⊢c-subst (⊢c-∀ cloA) newΓ upT cloT (st-∀ up stA) = {!!}


⊢c-subst0 : Γ ,= T ⊢c A
          → Γ ⊢c T
          → ⟦ T ⟧ A ⇘ A*
          → Γ ⊢c A*
⊢c-subst0 cloA cloT stA = ⊢c-subst cloA ◀Z {!!} cloA stA          
