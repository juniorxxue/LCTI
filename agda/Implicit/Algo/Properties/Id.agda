module Implicit.Algo.Properties.Id where

open import Implicit.Language.All
open import Implicit.Algo.Base
open import Implicit.Algo.Properties.Split

⊢id : Γ ⊢ Σ ⇒ e ⇒ A
    → ⟦ Σ , A ⟧→⟦ τ T , A' ⟧
    → T ≡ A'

s-id : Γ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B
     → ⟦ Σ , B ⟧→⟦ τ T , B' ⟧
     → T ≡ B'
s-id (s-type ss) none-τ = refl
s-id (s-term-c cloA ap ⊢e s) (have-e spl) = s-id s spl
s-id (s-term-o opnA ⊢e x s) (have-e spl) = s-id s spl
s-id {T = T} {B' = B'} (s-∀l s upᶜ upᵉ upC upD) spl'@(have-e spl)
  with ⟨ T′ , upT  ⟩ ← ↑ty0-total T
  with ⟨ B″ , upB' ⟩ ← ↑ty0-total B'
  with s-id s (spl-↑ty0 spl' (↑tyᶜ-e upᵉ upᶜ) (↑ty-arr upC upD) upT upB')
... | refl = ↑ty-unique-inver upT upB'

⊢id (⊢app ⊢e) spl = ⊢id ⊢e (have-e spl)
⊢id (⊢lam₁ ⊢e) none-τ rewrite ⊢id ⊢e none-τ = refl
⊢id (⊢lam₂ ⊢e up-c ⊢e₁) (have-e spl) = ⊢id ⊢e₁ (spl-↑tmᶜ0 spl up-c)
⊢id (⊢sub ⊢e ne gc s) spl = s-id s spl

-- corollaries
⊢id0 : Γ ⊢ τ B ⇒ e ⇒ A
     → B ≡ A
⊢id0 ⊢e = ⊢id ⊢e none-τ

s-id0 : Γ ⊢ A ≤⁺ τ B ⊣ Γ' ↪ C
      → B ≡ C
s-id0 (s-type ss) = refl
