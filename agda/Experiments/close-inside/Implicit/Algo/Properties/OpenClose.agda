module Implicit.Algo.Properties.OpenClose where

open import Implicit.Language
open import Implicit.Algo.Base
open import Implicit.Algo.Properties.Extension

----------------------------------------------------------------------
--+                       Lemmas around ⊢cᶜ                        +--
----------------------------------------------------------------------

⊢cᶜ-weaken^0 : Γ ⊢cᶜ Σ
             → ↑tyᶜ0 Σ ⇘ Σ'
             → Γ ,^ ⊢cᶜ Σ'
⊢cᶜ-weaken^0 ⊢c-empty ↑tyᶜ-□ = ⊢c-empty
⊢cᶜ-weaken^0 (⊢c-τ cloA) (↑tyᶜ-τ up-t) = ⊢c-τ (⊢c-weaken^0 cloA up-t)
⊢cᶜ-weaken^0 (⊢c-term cloe cloΣ) (↑tyᶜ-e up-e upΣ) = ⊢c-term (⊢cᵉ-weaken^0 cloe up-e) (⊢cᶜ-weaken^0 cloΣ upΣ)

⊢cᶜ-weaken,0 : Γ ⊢cᶜ Σ
             → ↑tmᶜ0 Σ ⇘ Σ'
             → Γ , A ⊢cᶜ Σ'
⊢cᶜ-weaken,0 ⊢c-empty ↑tmᶜ-□ = ⊢c-empty
⊢cᶜ-weaken,0 (⊢c-τ cloA) ↑tmᶜ-τ = ⊢c-τ (⊢c-weaken,0 cloA)
⊢cᶜ-weaken,0 (⊢c-term cloe cloΣ) (↑tmᶜ-e up-e upΣ) = ⊢c-term (⊢cᵉ-weaken,0 cloe up-e) (⊢cᶜ-weaken,0 cloΣ upΣ)

⊢cᶜ-strengthen,0 : Γ , A ⊢cᶜ Σ'
                → ↑tmᶜ0 Σ ⇘ Σ'
                → Γ ⊢cᶜ Σ
⊢cᶜ-strengthen,0 ⊢c-empty ↑tmᶜ-□ = ⊢c-empty
⊢cᶜ-strengthen,0 (⊢c-τ cloA) ↑tmᶜ-τ = ⊢c-τ (⊢c-strengthen,0 cloA)
⊢cᶜ-strengthen,0 (⊢c-term cloe cloΣ) (↑tmᶜ-e up-e upΣ) = ⊢c-term (⊢cᵉ-strengthen,0 cloe up-e) (⊢cᶜ-strengthen,0 cloΣ upΣ)

----------------------------------------------------------------------
--+                           Extension                            +--
----------------------------------------------------------------------

⊆-cloAᵉ : Γ ⊢cᵉ e
          → Γ ⊆ Γ'
          → Γ' ⊢cᵉ e
⊆-cloAᵉ ⊢c-lit ss = ⊢c-lit
⊆-cloAᵉ ⊢c-var ss = ⊢c-var
⊆-cloAᵉ (⊢c-lam clo) ss = ⊢c-lam (⊆-cloAᵉ clo (var ss))
⊆-cloAᵉ (⊢c-app clo clo₁) ss = ⊢c-app (⊆-cloAᵉ clo ss) (⊆-cloAᵉ clo₁ ss)
⊆-cloAᵉ (⊢c-ann x clo) ss = ⊢c-ann (⊆-cloA x ss) (⊆-cloAᵉ clo ss)
⊆-cloAᵉ (⊢c-tlam clo) ss = ⊢c-tlam (⊆-cloAᵉ clo (uvar ss))

⊆-cloAᶜ : Γ ⊢cᶜ Σ
          → Γ ⊆ Γ'
          → Γ' ⊢cᶜ Σ
⊆-cloAᶜ ⊢c-empty ss = ⊢c-empty
⊆-cloAᶜ (⊢c-τ cloA) ss = ⊢c-τ (⊆-cloA cloA ss)
⊆-cloAᶜ (⊢c-term cloe clo) ss = ⊢c-term (⊆-cloAᵉ cloe ss) (⊆-cloAᶜ clo ss)
