module Implicit.Algo.Properties.Split where

open import Implicit.Language.All
open import Implicit.Algo.Base
open import Implicit.Algo.Properties.Shift

sspl-unique :
    ⟦ Σ , A ⟧→⟦ Σ₁ ,  A₁ ⟧
  → ⟦ Σ , A ⟧→⟦ Σ₂ ,  A₂ ⟧
  → Σ₁ ≡ Σ₂ × A₁ ≡ A₂
sspl-unique none-□ none-□ = ⟨ refl , refl ⟩
sspl-unique none-τ none-τ = ⟨ refl , refl ⟩
sspl-unique (have-e spl1) (have-e spl2) = sspl-unique spl1 spl2

spl-↑tmᶜ0 : ⟦ Σ , A ⟧→⟦ τ T ,  A' ⟧
         → ↑tmᶜ0 Σ ⇘ Σ'
         → ⟦ Σ' , A ⟧→⟦ τ T ,  A' ⟧
spl-↑tmᶜ0 none-τ ↑tmᶜ-τ = none-τ
spl-↑tmᶜ0 (have-e spl) (↑tmᶜ-e up-e upΣ) = have-e (spl-↑tmᶜ0 spl upΣ)

≊-weaken : Σ₁ ≊ Σ₂
         → ↑tmᶜ0 Σ₁ ⇘ Σ₁'
         → ↑tmᶜ0 Σ₂ ⇘ Σ₂'
         → Σ₁' ≊ Σ₂'
≊-weaken ≊Z ↑tmᶜ-□ ↑tmᶜ-τ = ≊Z
≊-weaken (≊S eq) (↑tmᶜ-e up-e up1) (↑tmᶜ-e up-e₁ up2) rewrite ↑tm-unique up-e up-e₁ = ≊S (≊-weaken eq up1 up2)

spl-↑ty0 : ⟦ Σ , A ⟧→⟦ τ T , B ⟧
         → ↑tyᶜ0 Σ ⇘ Σ'
         → ↑ty0 A ⇘ A'
         → ↑ty0 T ⇘ T'
         → ↑ty0 B ⇘ B'
         → ⟦ Σ' , A' ⟧→⟦ τ T' , B' ⟧
spl-↑ty0 none-τ (↑tyᶜ-τ up-t) up2 up3 up4 with ↑ty-unique up-t up3 | ↑ty-unique up2 up4
... | refl | refl = none-τ
spl-↑ty0 (have-e spl) (↑tyᶜ-e up-e up1) (↑ty-arr up2 up5) up3 up4 = have-e (spl-↑ty0 spl up1 up5 up3 up4)

≊-↑ty0 : Σ₁ ≊ Σ₂
       → ↑tyᶜ0 Σ₁ ⇘ Σ₁'
       → ↑tyᶜ0 Σ₂ ⇘ Σ₂'
       → Σ₁' ≊ Σ₂'
≊-↑ty0 ≊Z ↑tyᶜ-□ (↑tyᶜ-τ up-t) = ≊Z
≊-↑ty0 (≊S newΣ) (↑tyᶜ-e up-e up1) (↑tyᶜ-e up-e₁ up2) with refl ← ↑tyᵉ-unique up-e up-e₁ = ≊S (≊-↑ty0 newΣ up1 up2)
