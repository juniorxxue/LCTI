module Implicit.Language.OpenClose.Strengthen where

open import Implicit.Language.Base
open import Implicit.Language.Lookup
open import Implicit.Language.Shift
open import Implicit.Language.Subst
open import Implicit.Language.OpenClose.Base

-- subst lemma implies this, only with condition Γ ⊢c T, but obviously we need less to prove this lemam
postulate
  ⊢c-strengthen=0 : Γ ,= T ⊢c A'
                  → ↑ty0 A ⇘ A'
                  → Γ ⊢c A

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
