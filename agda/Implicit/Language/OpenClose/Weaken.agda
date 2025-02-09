module Implicit.Language.OpenClose.Weaken where

open import Implicit.Language.Base
open import Implicit.Language.Lookup.All
open import Implicit.Language.Shift.All
open import Implicit.Language.Subst.All
open import Implicit.Language.OpenClose.Base
open import Implicit.Language.EnvOps.All

⊢c-weaken, : Γ ⊢c A
           → Γ ▶ k , T ⇘ Γ'
           → Γ' ⊢c A
⊢c-weaken, ⊢c-int extΓ = ⊢c-int
⊢c-weaken, (⊢c-var-∙ inΓ) extΓ = ⊢c-var-∙ (▶,-∋∙ inΓ extΓ)
⊢c-weaken, (⊢c-var-= inΓ) extΓ = ⊢c-var-= (▶,-∋= inΓ extΓ)
⊢c-weaken, (⊢c-arr clo clo₁) extΓ = ⊢c-arr (⊢c-weaken, clo extΓ) (⊢c-weaken, clo₁ extΓ)
⊢c-weaken, {T = T} (⊢c-∀ clo) extΓ = ⊢c-∀ (⊢c-weaken, clo (▶S∙ extΓ (proj₂ (↑ty0-total T))))

⊢c-weaken,0 : Γ ⊢c A
            → Γ ⊢c B
            → Γ , B ⊢c A
⊢c-weaken,0 clo cloB = ⊢c-weaken, clo (▶Z cloB)

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
            → Γ ⊢c B
            → Γ ,= B ⊢c A'
⊢c-weaken=0 clo upA cloB = ⊢c-weaken= clo (▶Z cloB) upA

----------------------------------------------------------------------
--+                       lemmas about ⊢cᵉ                         +--
----------------------------------------------------------------------

⊢cᵉ-weaken, : Γ ⊢cᵉ e
            → Γ ▶ k , T ⇘ Γ'
            → e ↑tm k ⇘ e'
            → Γ' ⊢cᵉ e'
⊢cᵉ-weaken, ⊢c-lit newΓ ↑tm-lit = ⊢c-lit
⊢cᵉ-weaken, ⊢c-var newΓ ↑tm-var = ⊢c-var
⊢cᵉ-weaken, (⊢c-lam clo-e) newΓ (↑tm-ƛ up-e) = ⊢c-lam (⊢cᵉ-weaken, clo-e (▶S, newΓ) up-e)
⊢cᵉ-weaken, (⊢c-app clo-e clo-e₁) newΓ (↑tm-app up-e up-e₁) = ⊢c-app (⊢cᵉ-weaken, clo-e newΓ up-e)
                                                                     (⊢cᵉ-weaken, clo-e₁ newΓ up-e₁)
⊢cᵉ-weaken, (⊢c-ann cloA clo-e) newΓ (↑tm-⦂ up-e) = ⊢c-ann (⊢c-weaken, cloA newΓ) (⊢cᵉ-weaken, clo-e newΓ up-e)
⊢cᵉ-weaken, {T = T} (⊢c-tlam clo-e) newΓ (↑tm-Λ up-e) = ⊢c-tlam (⊢cᵉ-weaken, clo-e (▶S∙ newΓ (proj₂ (↑ty0-total T))) up-e)

⊢cᵉ-weaken,0 : Γ ⊢cᵉ e
             → ↑tm0 e ⇘ e'
             → Γ ⊢c T
             → Γ , T ⊢cᵉ e'
⊢cᵉ-weaken,0 clo-e up-e cloT = ⊢cᵉ-weaken, clo-e (▶Z cloT) up-e

⊢cᵉ-weaken^ : Γ ⊢cᵉ e
            → Γ ▶ k ,^⇘ Γ'
            → e ↑tyᵉ k ⇘ e'
            → Γ' ⊢cᵉ e'
⊢cᵉ-weaken^ ⊢c-lit newΓ ↑tyᵉ-lit = ⊢c-lit
⊢cᵉ-weaken^ ⊢c-var newΓ ↑tyᵉ-var = ⊢c-var
⊢cᵉ-weaken^ {k = k} (⊢c-lam {A = A} clo-e) newΓ (↑tyᵉ-ƛ up-e) = ⊢c-lam (⊢cᵉ-weaken^ clo-e (▶S, newΓ (proj₂ (↑ty-total A k))) up-e)
⊢cᵉ-weaken^ (⊢c-app clo-e clo-e₁) newΓ (↑tyᵉ-app up-e up-e₁) = ⊢c-app (⊢cᵉ-weaken^ clo-e newΓ up-e)
                                                                      (⊢cᵉ-weaken^ clo-e₁ newΓ up-e₁)
⊢cᵉ-weaken^ (⊢c-ann cloA clo-e) newΓ (↑tyᵉ-⦂ up-e up) = ⊢c-ann (⊢c-weaken^ cloA newΓ up) (⊢cᵉ-weaken^ clo-e newΓ up-e)
⊢cᵉ-weaken^ (⊢c-tlam clo-e) newΓ (↑tyᵉ-Λ up-e) = ⊢c-tlam (⊢cᵉ-weaken^ clo-e (▶S∙ newΓ) up-e)

⊢cᵉ-weaken^0 : Γ ⊢cᵉ e
             → ↑tyᵉ0 e ⇘ e'
             → Γ ,^ ⊢cᵉ e'
⊢cᵉ-weaken^0 clo-e up-e = ⊢cᵉ-weaken^ clo-e ▶Z up-e
