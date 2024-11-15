module Implicit.Algo.Properties.Split where

open import Implicit.Language
open import Implicit.Algo.Base

private variable
  Σ Σ' Σ₁ Σ₂ Σ* Σ'* : Context n m
  A A' A₁ A₂ T T* B A* : Type m
  e̅ : Apps n m
  A̅ : AppsType m

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
  
  
