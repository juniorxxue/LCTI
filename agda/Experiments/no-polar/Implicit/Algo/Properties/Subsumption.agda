module Implicit.Algo.Properties.Subsumption where

open import Implicit.Language
open import Implicit.Algo.Base
open import Implicit.Algo.Properties.Id
open import Implicit.Algo.Properties.OpenClose
open import Implicit.Algo.Properties.Extension
open import Implicit.Algo.Properties.Polarity
open import Implicit.Algo.Properties.Strengthen
open import Implicit.Algo.Properties.Weaken
open import Implicit.Algo.Properties.Shift
open import Implicit.Algo.Properties.Split
open import Implicit.Algo.Properties.Environments

postulate
  s-trans : Γ ⊢ A₁ ≤ Σ ⊣ Δ ↪ A₂
          → Δ ⊢ A₂ ≤ Σ' ⊣ Δ ↪ A₃ -- A₂ couldn't be open
          → Σ ≋ Σ'
          → Γ ⊢ A₁ ≤ Σ' ⊣ Δ ↪ A₃

  s-subst : Γ ,= T ⊢ A ≤ Σ' ⊣ Δ ,= T ↪ B
          → ⟦ T ⟧ A ⇘ A*
          → ⟦ T ⟧ B ⇘ B*
          → ↑tyᶜ0 Σ ⇘ Σ'
          → Γ ⊢ A* ≤ Σ ⊣ Δ ↪ B*

s-refl : Closed Γ
       → Γ ⊢c A
       → Γ ⊢ A ≤ τ A ⊣ Γ ↪ A
s-refl cloΓ cloA = {!!}

----------------------------------------------------------------------
--+                           Main Logic                           +--
----------------------------------------------------------------------

⊢to≤ : Γ ⊢ Σ ⇒ e ⇒ A
     → Γ ⊢ A ≤ Σ ⊣ Γ ↪ A

subsumption : Γ ⊢ Σ ⇒ e ⇒ A
            → Σ ≋ Σ'
            → Γ ⊢ A ≤ Σ' ⊣ Γ ↪ A'
            → Γ ⊢ Σ' ⇒ e ⇒ A'

-- corollary
subsumption0 : Γ ⊢ □ ⇒ e ⇒ A
             → Γ ⊢ A ≤ Σ ⊣ Γ ↪ A'
             → Γ ⊢ Σ ⇒ e ⇒ A'
subsumption0 ⊢e s = subsumption ⊢e ≋Z s


s-refined-p : Γ ⊢ A ≤ Σ ⊣ Δ ↪ B
            → Δ ⊢ B ≤ Σ ⊣ Δ ↪ B
s-refined-p s = {!!}

⊢to≤ (⊢lit cloΓ) = s-empty cloΓ ⊢c-int
⊢to≤ (⊢var cloΓ x∈Γ) = s-empty {!!} {!!}
⊢to≤ (⊢ann ⊢e) = {!!}
⊢to≤ (⊢app ⊢e) with ⊢to≤ ⊢e
... | s-term-c ⊢e₁ r = r
... | s-term-o opnA ⊢e₁ r r₁ = ⊥-elim (⊢c-⊢o-disjoint (⊢cloA ⊢e₁) opnA)
⊢to≤ (⊢lam₁ ⊢e) with ⊢id0 ⊢e
... | refl = {!!}
⊢to≤ (⊢lam₂ ⊢e up-c ⊢e₁) = s-term-c (subsumption0 ⊢e {!!}) (s-strengthen,0 (⊢to≤ ⊢e₁) up-c)
⊢to≤ (⊢sub ⊢e ne gc s) = {!!}
⊢to≤ (⊢tabs ⊢e) = {!!}
