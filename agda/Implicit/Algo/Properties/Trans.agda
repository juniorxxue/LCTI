module Implicit.Algo.Properties.Trans where

-- not exactly like transitivity in classic subtyping
-- since we don't subsume it
-- it only describes the relation between *updates contexts*, used in subsumption lemma in ⊢sub case

open import Implicit.Language
open import Implicit.Algo.Base
open import Implicit.Algo.Properties.Id
open import Implicit.Algo.Properties.OpenClose
open import Implicit.Algo.Properties.Extension

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


s-trans : Γ ⊢ A₁ ⌞ ≤ ⌝ Σ ⊣ Δ ↪ A₂
        → Δ ⊢ A₂ ⌞ ≤ ⌝ Σ' ⊣ Δ ↪ A₃
        → Σ ≊ Σ'
        → Γ ⊢ A₁ ⌞ ≤ ⌝ Σ' ⊣ Δ ↪ A₃
s-trans (s-empty clo) s2 ≊Z = s2
s-trans (s-term-c ⊢e s1) (s-term-c ⊢e₁ s2) (≊S newΣ) with ⊢id0 ⊢e | ⊢id0 ⊢e₁
... | refl | refl = s-term-c ⊢e (s-trans s1 s2 newΣ)
s-trans (s-term-c ⊢e s1) (s-term-o opnA ⊢e₁ s2 s3) newΣ =
  ⊥-elim (⊢c-⊢o-disjoint (⊆-closed (⊢closeA ⊢e) (s-⊆ s1)) opnA)
s-trans (s-term-o opnA ⊢e s1 s3) (s-term-c ⊢e₁ s2) (≊S newΣ) with ⊢id0 ⊢e₁
... | refl = s-term-o opnA ⊢e s1 (s-trans s3 s2 newΣ)
s-trans s@(s-term-o opnA ⊢e s1 s3) (s-term-o opnA₁ ⊢e₁ s2 s4) newΣ =
  ⊥-elim (⊢c-⊢o-disjoint (⊆-closed (⊢closeA ⊢e) (s-⊆ s)) opnA₁)
s-trans (s-∀l s1 upᶜ upᵉ st₁ st₂) s2 newΣ = {!!}
