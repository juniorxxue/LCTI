module Implicit.Algo.New.Subsumption where

open import Implicit.Language.All hiding (_⊆_)
open import Implicit.Algo.Base

⊢to≤ : Γ ⊢ Σ ⇒ e ⇒ A
     → Γ ⊢ A ≤⁺ Σ ⊣ Γ ↪ A

subsumption : Γ ⊢ Σ ⇒ e ⇒ A
             → Σ ≊ Σ'
             → Γ ⊢ A ≤⁺ Σ' ⊣ Δ ↪ A'
             → Γ ⊢ Σ' ⇒ e ⇒ A
subsumption {Σ' = τ A} ⊢e newΣ s = {!!}
subsumption {Σ' = [ e ]↝ Σ'} ⊢e newΣ s = {!!}
