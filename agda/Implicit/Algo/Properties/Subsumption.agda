module Implicit.Algo.Properties.Subsumption where

open import Implicit.Language
open import Implicit.Algo.Base
open import Implicit.Algo.Properties.Id
-- open import Implicit.Algo.Properties.OpenClose
open import Implicit.Algo.Properties.Extension

⊢to≤ : Γ ⊢ Σ ⇒ e ⇒ A
     → Γ ⊢ A ⌞ ≤⁺ ⌝ Σ ⊣ Γ ↪ A

subsumption : Γ ⊢ Σ ⇒ e ⇒ A
            → ⟦ Σ ⟧⇒⟦ e̅ , □ ⟧
            → e̅ ⊕ Σ'' := Σ'
            → Γ ⊢ A ⌞ ≤⁺ ⌝ Σ' ⊣ Δ ↪ A' -- Δ is Γ
            → Γ ⊢ Σ' ⇒ e ⇒ A'

⊢to≤ ⊢lit = s-empty ⊢c-int
⊢to≤ (⊢var x∈Γ) = s-empty {!!}
⊢to≤ (⊢ann ⊢e) = s-empty {!!}
⊢to≤ (⊢app ⊢e) with ⊢to≤ ⊢e
... | s-term-c cloA ⊢e₁ ih = ih
... | s-term-o opnA ⊢e₁ ih ih₁ = {!!}
⊢to≤ (⊢lam₁ ⊢e) with ⊢to≤ ⊢e
... | ih rewrite ⊢id0 ⊢e = {!!}
⊢to≤ (⊢lam₂ ⊢e up-c ⊢e₁) = {!!}
⊢to≤ (⊢sub ⊢e ne gc s) = {!!}
⊢to≤ (⊢tabs ⊢e) = {!!}





