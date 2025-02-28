module Implicit.Algo.Properties.NewTrans where

-- not exactly like transitivity in classic subtyping
-- since we don't subsume it
-- it only describes the relation between *updates contexts*, used in subsumption lemma in ⊢sub case

open import Implicit.Language.All
open import Implicit.Algo.Base
open import Implicit.Algo.Properties.Id
open import Implicit.Algo.Properties.OpenClose
open import Implicit.Algo.Properties.Polarity


s-trans : Γ ⊢ A₁ ⌞ ≤ ⌝ Σ ⊣ Δ ↪ A₂
        → Δ ⊢ A₂ ⌞ ≤ ⌝ Σ' ⊣ Δ ↪ A₃ -- A₂ couldn't be open
        → Σ ≊ Σ'
        → Γ ⊢ A₁ ⌞ ≤ ⌝ Σ' ⊣ Δ ↪ A₃
s-trans (s-empty clo) s2 newΣ = {!!}
s-trans (s-term-c ⊢e s1) s2 newΣ = {!!}
s-trans (s-term-o opnA ⊢e s1 s3) s2 newΣ = {!!}
s-trans (s-∀l s1 upᶜ upᵉ st₁ st₂) (s-term-c ⊢e s2) (≊S newΣ) =
  s-∀l (s-trans s1 (s-term-c {!!} {!!}) {!!}) {!!} {!!} {!!} {!!}
s-trans (s-∀l s1 upᶜ upᵉ st₁ st₂) (s-term-o opnA ⊢e s2 s3) newΣ = {!!}


{-
s-trans0 : Γ ⊢ A ⌞ ≤⁺ ⌝ Σ ⊣ Γ ↪ B
         → Σ ≊ Σ'
         → Γ ⊢ B ⌞ ≤⁺ ⌝ Σ' ⊣ Γ ↪ C
         → Γ ⊢ A ⌞ ≤⁺ ⌝ Σ' ⊣ Γ ↪ C
s-trans0 (s-empty clo) newΣ s2 = s2
s-trans0 (s-term-c ⊢e s1) (≊S newΣ) (s-term-c ⊢e₁ s2) = {!!}
s-trans0 (s-term-c ⊢e s1) newΣ (s-term-o opnA ⊢e₁ s2 s3) = {!!}
s-trans0 (s-term-o opnA ⊢e s1 s3) (≊S newΣ) s2 = {!!}
s-trans0 (s-∀l s1 upᶜ upᵉ st₁ st₂) (≊S newΣ) (s-term-c ⊢e s2) =
  s-∀l {!!} {!!} upᵉ {!!} {!!}
s-trans0 (s-∀l s1 upᶜ upᵉ st₁ st₂) newΣ (s-term-o opnA ⊢e s2 s3) = {!!}
-}
