module Implicit.Algo.Properties.Split where

open import Implicit.Language.All
open import Implicit.Algo.Base
open import Implicit.Algo.Properties.Shift

sspl-unique :
    ⟦ Σ , A ⟧→s⟦ Σ₁ ,  A₁ ⟧
  → ⟦ Σ , A ⟧→s⟦ Σ₂ ,  A₂ ⟧
  → Σ₁ ≡ Σ₂ × A₁ ≡ A₂
sspl-unique none-□ none-□ = ⟨ refl , refl ⟩
sspl-unique none-τ none-τ = ⟨ refl , refl ⟩
sspl-unique (have-e spl1) (have-e spl2) = sspl-unique spl1 spl2

spl→sspl :
    ⟦ Σ , A ⟧→⟦ e̅ , Σ' , A̅ , A' ⟧
  → ⟦ Σ , A ⟧→s⟦ Σ' , A' ⟧
spl→sspl none-□ = none-□
spl→sspl none-τ = none-τ
spl→sspl (have-e spl) = have-e (spl→sspl spl)

sspl-↑-st :
    ⟦ Σ , A ⟧→s⟦ Σ' , T ⟧
  → ⟦ B ⟧ᶜ Σ ⇘ Σ*
  → ⟦ B ⟧ᶜ Σ' ⇘ Σ'*
  → ⟦ B ⟧ A ⇘ A*
  → ⟦ B ⟧ T ⇘ T*
  → ⟦ Σ* , A* ⟧→s⟦ Σ'* , T* ⟧
sspl-↑-st none-□ empty empty st3 st4 rewrite st0-unique st3 st4 = none-□
sspl-↑-st none-τ (fulltype st1) (fulltype st2) st3 st4 rewrite st0-unique st1 st2 | st0-unique st3 st4 = none-τ
sspl-↑-st (have-e spl) (term st1 ste) st2 (st-arr st3 st5) st4 = have-e (sspl-↑-st spl st1 st2 st5 st4)

-- proof is generated
spl-↑tm :
    ⟦ Σ , A ⟧→⟦ e̅ , τ T , A̅ , A' ⟧
  → ↑tmᶜ0 Σ ⇘ Σ'
  → ∃[ e̅' ](⟦ Σ' , A ⟧→⟦ e̅' , τ T , A̅ , A' ⟧ × (↑tmᵃ0 e̅ ⇘ e̅'))
spl-↑tm none-τ ↑tmᶜ-τ = ⟨ nil , ⟨ none-τ , nil ⟩ ⟩
spl-↑tm (have-e spl) (↑tmᶜ-e {e' = e'} up-e up-c) = ⟨ e' ∷a spl-↑tm spl up-c .proj₁ ,
                                           ⟨ have-e (spl-↑tm spl up-c .proj₂ .proj₁) ,
                                           up-e ∷a spl-↑tm spl up-c .proj₂ .proj₂ ⟩ ⟩

