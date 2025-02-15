module Implicit.Algo.Properties.Trans where

-- not exactly like transitivity in classic subtyping
-- since we don't subsume it
-- it only describes the relation between *updates contexts*, used in subsumption lemma in ⊢sub case

open import Implicit.Language.All
open import Implicit.Algo.Base
open import Implicit.Algo.Properties.Id
open import Implicit.Algo.Properties.OpenClose
open import Implicit.Algo.Properties.Polarity

{-
looks like polar is not needed here
s-trans : Γ ⊢ A₁ ⌞ ≤ ⌝ Σ ⊣ Δ ↪ A₂
        → Γ ⊢ A₂ ⌞ ≤ ⌝ Σ' ⊣ Ψ ↪ A₃
        → Σ ≊ Σ'
        → Polarity Γ A₁ Σ ≤
        → Polarity Γ A₂ Σ' ≤
        → Γ ⊢ A₁ ⌞ ≤ ⌝ Σ' ⊣ Ψ ↪ A₃
s-trans (s-empty clo) s2 ≊Z pr1 pr2 = s2
s-trans (s-term-c ⊢e s1) s2 newΣ pr1 pr2 = {!!}
s-trans (s-term-o opnA ⊢e s1 s3) (s-term-c ⊢e₁ s2) (≊S newΣ) pr1 pr2 with ⊢id0 ⊢e₁
... | refl = s-term-o opnA ⊢e s1 (s-trans {!!} {!!} newΣ {!!} {!!})
s-trans (s-term-o opnA ⊢e s1 s3) (s-term-o opnA₁ ⊢e₁ s2 s4) (≊S newΣ) pr1 pr2 = {!!} -- false
s-trans (s-∀l s1 upᶜ upᵉ st₁ st₂) s2 newΣ pr1 pr2 = {!!}

-}

{-
---
Γ |- e : A              Γ |- 1 : Int   X = Int

Γ , X=Int |- [] => 1 => X

[T/x] A' == A
---------------------
Γ , x = T |- e : A'

---
-}

s-trans : Γ ⊢ A₁ ⌞ ≤ ⌝ Σ ⊣ Δ ↪ A₂
        → Δ ⊢ A₂ ⌞ ≤ ⌝ Σ' ⊣ Δ ↪ A₃ -- A₂ couldn't be open
        → Σ ≊ Σ'
        → Γ ⊢ A₁ ⌞ ≤ ⌝ Σ' ⊣ Δ ↪ A₃
s-trans (s-empty clo) s2 ≊Z = s2
s-trans (s-term-c ⊢e s1) (s-term-c ⊢e₁ s2) (≊S newΣ) with ⊢id0 ⊢e | ⊢id0 ⊢e₁
... | refl | refl = s-term-c ⊢e (s-trans s1 s2 newΣ)
s-trans (s-term-c ⊢e s1) (s-term-o opnA ⊢e₁ s2 s3) newΣ =
  ⊥-elim (⊢c-⊢o-disjoint (⊆-cloA (⊢closeA ⊢e) {!!}) opnA)
s-trans (s-term-o opnA ⊢e s1 s3) (s-term-c ⊢e₁ s2) (≊S newΣ) with ⊢id0 ⊢e₁
... | refl = s-term-o opnA ⊢e s1 (s-trans s3 s2 newΣ)
s-trans s@(s-term-o opnA ⊢e s1 s3) (s-term-o opnA₁ ⊢e₁ s2 s4) newΣ =
  ⊥-elim (⊢c-⊢o-disjoint (⊆-cloA (⊢closeA ⊢e) {!!}) opnA₁)
s-trans (s-∀l s1 upᶜ upᵉ st₁ st₂) (s-term-c ⊢e s2) (≊S newΣ) with ⊢id0 ⊢e
... | refl = {!!}
-- s-∀l (s-trans s1 (s-term-c {!!} {!!}) {!!}) {!!} {!!} {!!} {!!}
s-trans (s-∀l s1 upᶜ upᵉ st₁ st₂) (s-term-o opnA ⊢e s2 s3) newΣ = {!!}


{-

s-trans0 : Γ ⊢ A ⌞ ≤⁺ ⌝ Σ ⊣ Γ ↪ B
           → Σ ≊ Σ'
           → Γ ⊢ B ⌞ ≤⁺ ⌝ Σ' ⊣ Γ ↪ C
           → Γ ⊢ A ⌞ ≤⁺ ⌝ Σ' ⊣ Γ ↪ C
s-trans0 (s-empty clo) newΓ s2 = {!!}
s-trans0 (s-term-c ⊢e s1) newΓ s2 = {!!}
s-trans0 (s-term-o opnA ⊢e s1 s3) newΓ s2 = {!!}
s-trans0 (s-∀l s1 upᶜ upᵉ st₁ st₂) newΓ (s-term-c ⊢e s2) = {!!}
s-trans0 (s-∀l s1 upᶜ upᵉ st₁ st₂) newΓ (s-term-o opnA ⊢e s2 s3) = {!!} -- false
-}
