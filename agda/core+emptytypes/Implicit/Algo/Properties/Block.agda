module Implicit.Algo.Properties.Block where

open import Implicit.Language.All
open import Implicit.AuxLemmas
open import Implicit.Algo.Base


s-block : Γ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B
        → Γ ⊢⊠ B
s-block (s-empty regΓ cloA grd) = {!!}
s-block (s-type ss) = {!!}
s-block (s-term-c cloA ap ⊢e s) = {!!}
s-block (s-term-o opnA ⊢e ss s) = {!!}
s-block (s-∀l s upᶜ upᵉ upC upD) = {!!}
s-block (s-∀l-no s upᶜ upᵉ upC upD) = {!!}
s-block (s-tapp s upᶜ) = {!!}
s-block (s-svar-term x s) = s-block s
s-block (s-svar-tapp x s) = s-block s
s-block (s-evar-infers infs inst) = {!!}
