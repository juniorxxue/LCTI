module Implicit.Algo.Properties.NewTrans where

-- not exactly like transitivity in classic subtyping
-- since we don't subsume it
-- it only describes the relation between *updates contexts*, used in subsumption lemma in ⊢sub case

open import Implicit.Language.All
open import Implicit.Algo.Base
-- open import Implicit.Algo.Properties.Id
-- open import Implicit.Algo.Properties.OpenClose
-- open import Implicit.Algo.Properties.Polarity


s-trans : Γ ⊢ A₁ ⌞ ≤ ⌝ Σ ⊣ Δ ↪ A₂
        → Δ ⊢ A₂ ⌞ ≤ ⌝ Σ' ⊣ Δ ↪ A₃ -- A₂ couldn't be open
        → Σ ≊ Σ'
        → Γ ⊢ A₁ ⌞ ≤ ⌝ Σ' ⊣ Δ ↪ A₃
s-trans (s-empty cloΓ clo x) s2 newΣ = {!!}
s-trans (s-term-c cloA ap ⊢e s1) s2 newΣ = {!!}
s-trans (s-term-o opnA ⊢e s1 s3) s2 newΣ = {!!}
s-trans (s-∀l s1 upᶜ upᵉ upC upD) (s-term-c cloA ap ⊢e s2) newΣ =
  s-∀l (s-trans s1 (s-term-c {!!} {!!} {!!} {!!}) {!!}) {!!} {!!} {!!} {!!}
s-trans (s-∀l s1 upᶜ upᵉ upC upD) (s-term-o opnA ⊢e s2 s3) newΣ = {!!}
