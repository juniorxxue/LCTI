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

⊢cᶜ-weaken=0 : Γ ⊢cᶜ Σ
             → ↑tyᶜ0 Σ ⇘ Σ'
             → Γ ⊢c T
             → Γ ,= T ⊢cᶜ Σ'
⊢cᶜ-weaken=0 ⊢c-empty ↑tyᶜ-□ cloT = ⊢c-empty
⊢cᶜ-weaken=0 (⊢c-τ cloA) (↑tyᶜ-τ up-t) cloT = ⊢c-τ (⊢c-weaken=0 cloA up-t cloT)
⊢cᶜ-weaken=0 (⊢c-term cloe clo) (↑tyᶜ-e up-e up) cloT = ⊢c-term (⊢cᵉ-weaken=0 cloe cloT up-e) (⊢cᶜ-weaken=0 clo up cloT)

⊢cᶜ-weaken,0 : Γ ⊢cᶜ Σ
             → ↑tmᶜ0 Σ ⇘ Σ'
             → Γ ⊢c A
             → Γ , A ⊢cᶜ Σ'
⊢cᶜ-weaken,0 ⊢c-empty ↑tmᶜ-□ cloA = ⊢c-empty
⊢cᶜ-weaken,0 (⊢c-τ cloA) ↑tmᶜ-τ cloA' = ⊢c-τ (⊢c-weaken,0 cloA cloA')
⊢cᶜ-weaken,0 (⊢c-term cloe cloΣ) (↑tmᶜ-e up-e upΣ) cloA = ⊢c-term (⊢cᵉ-weaken,0 cloe up-e cloA) (⊢cᶜ-weaken,0 cloΣ upΣ cloA)

⊢cᶜ-strengthen,0 : Γ , A ⊢cᶜ Σ'
                → ↑tmᶜ0 Σ ⇘ Σ'
                → Γ ⊢cᶜ Σ
⊢cᶜ-strengthen,0 ⊢c-empty ↑tmᶜ-□ = ⊢c-empty
⊢cᶜ-strengthen,0 (⊢c-τ cloA) ↑tmᶜ-τ = ⊢c-τ (⊢c-strengthen,0 cloA)
⊢cᶜ-strengthen,0 (⊢c-term cloe cloΣ) (↑tmᶜ-e up-e upΣ) = ⊢c-term (⊢cᵉ-strengthen,0 cloe up-e) (⊢cᶜ-strengthen,0 cloΣ upΣ)

⊢cᶜ-strengthen=0 : Γ ,= A ⊢cᶜ Σ'
                 → ↑tyᶜ0 Σ ⇘ Σ'
                 → Γ ⊢cᶜ Σ
⊢cᶜ-strengthen=0 ⊢c-empty ↑tyᶜ-□ = ⊢c-empty
⊢cᶜ-strengthen=0 (⊢c-τ cloA) (↑tyᶜ-τ up-t) = ⊢c-τ (⊢c-strengthen=0 cloA up-t)
⊢cᶜ-strengthen=0 (⊢c-term cloe clo) (↑tyᶜ-e up-e up) = ⊢c-term (⊢cᵉ-strengthen=0 cloe up-e) (⊢cᶜ-strengthen=0 clo up)

----------------------------------------------------------------------
--+                           Extension                            +--
----------------------------------------------------------------------

⊆-cloᵉ : Γ ⊢cᵉ e
        → Γ ⊆ Γ'
        → Γ' ⊢cᵉ e
⊆-cloᵉ ⊢c-lit ss = ⊢c-lit
⊆-cloᵉ ⊢c-var ss = ⊢c-var
⊆-cloᵉ (⊢c-lam clo) ss = ⊢c-lam (⊆-cloᵉ clo (var ss))
⊆-cloᵉ (⊢c-app clo clo₁) ss = ⊢c-app (⊆-cloᵉ clo ss) (⊆-cloᵉ clo₁ ss)
⊆-cloᵉ (⊢c-ann x clo) ss = ⊢c-ann (⊆-cloA x ss) (⊆-cloᵉ clo ss)
⊆-cloᵉ (⊢c-tlam clo) ss = ⊢c-tlam (⊆-cloᵉ clo (uvar ss))

⊆-cloᶜ : Γ ⊢cᶜ Σ
        → Γ ⊆ Γ'
        → Γ' ⊢cᶜ Σ
⊆-cloᶜ ⊢c-empty ss = ⊢c-empty
⊆-cloᶜ (⊢c-τ clo) ss = ⊢c-τ (⊆-cloA clo ss)
⊆-cloᶜ (⊢c-term cloe clo) ss = ⊢c-term (⊆-cloᵉ cloe ss) (⊆-cloᶜ clo ss)
