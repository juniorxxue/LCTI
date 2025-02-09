module Implicit.Language.OpenClose.Strengthen where

open import Implicit.Language.Base
open import Implicit.Language.Lookup.All
open import Implicit.Language.Shift.All
open import Implicit.Language.Subst.All
open import Implicit.Language.OpenClose.Base
open import Implicit.Language.EnvOps.Base
open import Implicit.Language.EnvOps.Insert
open import Implicit.Language.EnvOps.Remove

-- subst lemma implies this, only with condition Γ ⊢c T, but obviously we need less to prove this lemam
⊢c-strengthen, : Γ ⊢c A
               → Γ ◀ k ,⇘ Γ'
               → Γ' ⊢c A
⊢c-strengthen, ⊢c-int newΓ' = ⊢c-int
⊢c-strengthen, (⊢c-var-∙ inΓ) newΓ' = ⊢c-var-∙ (◀,-∋∙ inΓ newΓ')
⊢c-strengthen, (⊢c-var-= inΓ) newΓ' = ⊢c-var-= (◀,-∋= inΓ newΓ')
⊢c-strengthen, (⊢c-arr clo clo₁) newΓ' = ⊢c-arr (⊢c-strengthen, clo newΓ') (⊢c-strengthen, clo₁ newΓ')
⊢c-strengthen, (⊢c-∀ clo) newΓ' = ⊢c-∀ (⊢c-strengthen, clo (◀S∙ newΓ'))

⊢c-strengthen,0 : Γ , B ⊢c A
                → Γ ⊢c A
⊢c-strengthen,0 clo = ⊢c-strengthen, clo ◀Z

⊢c-strengthen^ : Γ ⊢c A'
               → Γ ◀ k ^⇘ Γ'
               → A ↑ty k ⇘ A'
               → Γ' ⊢c A
⊢c-strengthen^ ⊢c-int newΓ ↑ty-int = ⊢c-int
⊢c-strengthen^ (⊢c-var-∙ inΓ) newΓ ↑ty-var = ⊢c-var-∙ (◀^-∋∙ inΓ newΓ)
⊢c-strengthen^ (⊢c-var-= inΓ) newΓ ↑ty-var = ⊢c-var-= (◀^-∋= inΓ newΓ)
⊢c-strengthen^ (⊢c-arr clo clo₁) newΓ (↑ty-arr upA upA₁) =
  ⊢c-arr (⊢c-strengthen^ clo newΓ upA) (⊢c-strengthen^ clo₁ newΓ upA₁)
⊢c-strengthen^ (⊢c-∀ clo) newΓ (↑ty-∀ upA) = ⊢c-∀ (⊢c-strengthen^ clo (◀S∙ newΓ) upA)

⊢c-strengthen^0 : Γ ,^ ⊢c A'
                → ↑ty0 A ⇘ A'
                → Γ ⊢c A
⊢c-strengthen^0 clo up = ⊢c-strengthen^ clo ◀Z up

-- try to prove strengthen with ▶
⊢c-strengthen∙ : Γ' ⊢c A'
               → Γ ▶ k ,∙⇘ Γ'
               → A ↑ty k ⇘ A'
               → Γ ⊢c A
⊢c-strengthen∙ ⊢c-int newΓ ↑ty-int = ⊢c-int
⊢c-strengthen∙ (⊢c-var-∙ inΓ) newΓ ↑ty-var = ⊢c-var-∙ (▶∙-∋∙-rev inΓ newΓ)
⊢c-strengthen∙ (⊢c-var-= inΓ) newΓ ↑ty-var = ⊢c-var-= (▶∙-∋=-rev inΓ newΓ)
⊢c-strengthen∙ (⊢c-arr inΓ inΓ₁) newΓ (↑ty-arr upA upA₁) = ⊢c-arr (⊢c-strengthen∙ inΓ newΓ upA)
                                                                  (⊢c-strengthen∙ inΓ₁ newΓ upA₁)
⊢c-strengthen∙ (⊢c-∀ inΓ) newΓ (↑ty-∀ upA) = ⊢c-∀ (⊢c-strengthen∙ inΓ (▶S∙ newΓ) upA)


⊢c-strengthen∙0 : Γ ,∙ ⊢c A'
                → ↑ty0 A ⇘ A'
                → Γ ⊢c A
⊢c-strengthen∙0 clo up = ⊢c-strengthen∙ clo ▶Z up



⊢c-strengthen= : Γ ⊢c A'
               → Γ ◀ k =⇘ Γ'
               → A ↑ty k ⇘ A'
               → Γ' ⊢c A
⊢c-strengthen= ⊢c-int newΓ ↑ty-int = ⊢c-int
⊢c-strengthen= (⊢c-var-∙ inΓ) newΓ ↑ty-var = ⊢c-var-∙ (◀=-∋∙ inΓ newΓ)
⊢c-strengthen= (⊢c-var-= inΓ) newΓ ↑ty-var = ⊢c-var-= (◀=-∋= inΓ newΓ)
⊢c-strengthen= (⊢c-arr cloA cloA₁) newΓ (↑ty-arr upA upA₁) = ⊢c-arr (⊢c-strengthen= cloA newΓ upA)
                                                                    (⊢c-strengthen= cloA₁ newΓ upA₁)
⊢c-strengthen= (⊢c-∀ cloA) newΓ (↑ty-∀ upA) = ⊢c-∀ (⊢c-strengthen= cloA (◀S∙ newΓ) upA)


⊢c-strengthen=0 : Γ ,= T ⊢c A'
                → ↑ty0 A ⇘ A'
                → Γ ⊢c A
⊢c-strengthen=0 cloA upA = ⊢c-strengthen= cloA ◀Z upA

----------------------------------------------------------------------
--+                       lemmas about ⊢cᵉ                         +--
----------------------------------------------------------------------

⊢cᵉ-strengthen, : Γ ⊢cᵉ e'
                → Γ ◀ k ,⇘ Γ'
                → e ↑tm k ⇘ e'
                → Γ' ⊢cᵉ e
⊢cᵉ-strengthen, ⊢c-lit newΓ ↑tm-lit = ⊢c-lit
⊢cᵉ-strengthen, ⊢c-var newΓ ↑tm-var = ⊢c-var
⊢cᵉ-strengthen, (⊢c-lam clo-e) newΓ (↑tm-ƛ up-e) = ⊢c-lam (⊢cᵉ-strengthen, clo-e (◀S, newΓ) up-e)
⊢cᵉ-strengthen, (⊢c-app clo-e clo-e₁) newΓ (↑tm-app up-e up-e₁) = ⊢c-app (⊢cᵉ-strengthen, clo-e newΓ up-e)
                                                                         (⊢cᵉ-strengthen, clo-e₁ newΓ up-e₁)
⊢cᵉ-strengthen, (⊢c-ann cloA clo-e) newΓ (↑tm-⦂ up-e) = ⊢c-ann (⊢c-strengthen, cloA newΓ) (⊢cᵉ-strengthen, clo-e newΓ up-e)
⊢cᵉ-strengthen, (⊢c-tlam clo-e) newΓ (↑tm-Λ up-e) = ⊢c-tlam (⊢cᵉ-strengthen, clo-e (◀S∙ newΓ) up-e)

⊢cᵉ-strengthen,0 : Γ , A ⊢cᵉ e'
                 → ↑tm0 e ⇘ e'
                 → Γ ⊢cᵉ e
⊢cᵉ-strengthen,0 clo-e up-e = ⊢cᵉ-strengthen, clo-e ◀Z up-e

----------------------------------------------------------------------
--+                             closed                             +--
----------------------------------------------------------------------


closed-strengthen, : Closed Γ
                   → Γ ◀ k ,⇘ Γ'
                   → Closed Γ'
closed-strengthen, (clo-S, cloΓ cloA) ◀Z = cloΓ
closed-strengthen, (clo-S, cloΓ cloA) (◀S, newΓ) = clo-S, (closed-strengthen, cloΓ newΓ) (⊢c-strengthen, cloA newΓ)
closed-strengthen, (clo-S∙ cloΓ) (◀S∙ newΓ) = clo-S∙ (closed-strengthen, cloΓ newΓ)
closed-strengthen, (clo-S^ cloΓ) (◀S^ newΓ) = clo-S^ (closed-strengthen, cloΓ newΓ)
closed-strengthen, (clo-S= cloΓ cloA) (◀S= newΓ) = clo-S= (closed-strengthen, cloΓ newΓ) (⊢c-strengthen, cloA newΓ)
