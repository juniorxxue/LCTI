module Implicit.Algo.New.Trans where

open import Implicit.Language.All hiding (_⊆_)
open import Implicit.Algo.Base

postulate
  ⊢id0 : Γ ⊢ τ A ⇒ e ⇒ B
       → A ≡ B

s-trans : Γ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B
        → Δ ⊢ B ≤⁺ Σ' ⊣ Δ ↪ C
        → Σ ≊ Σ'
        → Γ ⊢ A ≤⁺ Σ' ⊣ Δ ↪ C
s-trans (s-empty cloΓ cloA x) s2 ≊Z = {!!} -- a new property needed
s-trans (s-term-c cloA ap ⊢e s1) (s-term-c cloA₁ ap₁ ⊢e₁ s2) (≊S newΣ) with ⊢id0 ⊢e | ⊢id0 ⊢e₁
... | refl | refl = s-term-c cloA {!!} {!!} (s-trans s1 s2 newΣ)
s-trans (s-term-c cloA ap ⊢e s1) (s-term-o opnA ⊢e₁ x s2) (≊S newΣ) = ⊥-elim {!!}
s-trans (s-term-o opnA ⊢e x s1) (s-term-c cloA ap ⊢e₁ s2) (≊S newΣ) = s-term-o opnA {!!} {!!} (s-trans s1 s2 newΣ)
s-trans (s-term-o opnA ⊢e x s1) (s-term-o opnA₁ ⊢e₁ x₁ s2) newΣ = ⊥-elim {!!}
s-trans (s-∀l s1 upᶜ upᵉ upC upD) s'@(s-term-c cloA ap ⊢e s2) (≊S newΣ) = s-∀l (s-trans s1 {!!} {!!}) {!!} {!!} {!!} {!!}
s-trans (s-∀l s1 upᶜ upᵉ upC upD) (s-term-o opnA ⊢e x s2) (≊S newΣ) = ⊥-elim {!!}
