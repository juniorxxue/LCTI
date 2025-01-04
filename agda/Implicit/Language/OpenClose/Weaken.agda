module Implicit.Language.OpenClose.Weaken where

open import Implicit.Language.Base
open import Implicit.Language.Lookup
open import Implicit.Language.Shift
open import Implicit.Language.Subst
open import Implicit.Language.OpenClose.Base

⊢c-weaken, : Γ ⊢c A
           → Γ ▶ k , T ⇘ Γ'
           → Γ' ⊢c A
⊢c-weaken, ⊢c-int extΓ = ⊢c-int
⊢c-weaken, (⊢c-var-∙ inΓ) extΓ = ⊢c-var-∙ (▶,-∋∙ inΓ extΓ)
⊢c-weaken, (⊢c-var-= inΓ) extΓ = ⊢c-var-= (▶,-∋= inΓ extΓ)
⊢c-weaken, (⊢c-arr clo clo₁) extΓ = ⊢c-arr (⊢c-weaken, clo extΓ) (⊢c-weaken, clo₁ extΓ)
⊢c-weaken, {T = T} (⊢c-∀ clo) extΓ = ⊢c-∀ (⊢c-weaken, clo (▶S∙ extΓ (proj₂ (↑ty0-total T))))

⊢c-weaken,0 : Γ ⊢c A → Γ , B ⊢c A
⊢c-weaken,0 clo = ⊢c-weaken, clo ▶Z

⊢c-weaken^ : Γ ⊢c A
           → Γ ▶ k ,^⇘ Γ'
           → A ↑ty k ⇘ A'
           → Γ' ⊢c A'
⊢c-weaken^ ⊢c-int extΓ' ↑ty-int = ⊢c-int
⊢c-weaken^ (⊢c-var-∙ inΓ) extΓ' ↑ty-var = ⊢c-var-∙ (▶^-∋∙ inΓ extΓ')
⊢c-weaken^ (⊢c-var-= inΓ) extΓ' ↑ty-var = ⊢c-var-= (▶^-∋= inΓ extΓ')
⊢c-weaken^ (⊢c-arr clo clo₁) extΓ' (↑ty-arr upA upA₁) = ⊢c-arr (⊢c-weaken^ clo extΓ' upA) (⊢c-weaken^ clo₁ extΓ' upA₁)
⊢c-weaken^ (⊢c-∀ clo) extΓ' (↑ty-∀ upA) = ⊢c-∀ (⊢c-weaken^ clo (▶S∙ extΓ') upA)

⊢c-weaken^0 : Γ ⊢c A
            → ↑ty0 A ⇘ A'
            → Γ ,^ ⊢c A'
⊢c-weaken^0 clo upA = ⊢c-weaken^ clo ▶Z upA


⊢c-weaken∙ : Γ ⊢c A
           → Γ ▶ k ,∙⇘ Γ'
           → A ↑ty k ⇘ A'
           → Γ' ⊢c A'
⊢c-weaken∙ ⊢c-int extΓ' ↑ty-int = ⊢c-int
⊢c-weaken∙ (⊢c-var-∙ inΓ) extΓ' ↑ty-var = ⊢c-var-∙ (▶∙-∋∙ inΓ extΓ')
⊢c-weaken∙ (⊢c-var-= inΓ) extΓ' ↑ty-var = ⊢c-var-= (▶∙-∋= inΓ extΓ')
⊢c-weaken∙ (⊢c-arr clo clo₁) extΓ' (↑ty-arr upA upA₁) = ⊢c-arr (⊢c-weaken∙ clo extΓ' upA) (⊢c-weaken∙ clo₁ extΓ' upA₁)
⊢c-weaken∙ (⊢c-∀ clo) extΓ' (↑ty-∀ upA) = ⊢c-∀ (⊢c-weaken∙ clo (▶S∙ extΓ') upA)

⊢c-weaken∙0 : Γ ⊢c A
            → ↑ty0 A ⇘ A'
            → Γ ,∙ ⊢c A'
⊢c-weaken∙0 clo upA = ⊢c-weaken∙ clo ▶Z upA

⊢c-weaken= : Γ ⊢c A
           → Γ ▶ k ,= T ⇘ Γ'
           → A ↑ty k ⇘ A'
           → Γ' ⊢c A'
⊢c-weaken= ⊢c-int newΓ ↑ty-int = ⊢c-int
⊢c-weaken= (⊢c-var-∙ inΓ) newΓ ↑ty-var = ⊢c-var-∙ (▶=-∋∙ inΓ newΓ)
⊢c-weaken= (⊢c-var-= inΓ) newΓ ↑ty-var = ⊢c-var-= (▶=-∋= inΓ newΓ)
⊢c-weaken= (⊢c-arr cloA cloA₁) newΓ (↑ty-arr upA upA₁) = ⊢c-arr (⊢c-weaken= cloA newΓ upA) (⊢c-weaken= cloA₁ newΓ upA₁)
⊢c-weaken= {T = T} (⊢c-∀ cloA) newΓ (↑ty-∀ upA) = ⊢c-∀ (⊢c-weaken= cloA (▶S∙ newΓ (proj₂ (↑ty0-total T))) upA)

⊢c-weaken=0 : Γ ⊢c A
            → ↑ty0 A ⇘ A'
            → Γ ,= B ⊢c A'
⊢c-weaken=0 clo upA = ⊢c-weaken= clo ▶Z upA
