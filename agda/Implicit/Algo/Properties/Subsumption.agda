module Implicit.Algo.Properties.Subsumption where

open import Implicit.Language
open import Implicit.Algo.Base
open import Implicit.Algo.Properties.Id
open import Implicit.Algo.Properties.OpenClose
open import Implicit.Algo.Properties.Extension
open import Implicit.Algo.Properties.Strengthen

s-refl : Γ ⊢ A ⌞ ≤ ⌝ τ A ⊣ Γ ↪ A
s-refl {A = Int} = s-int
s-refl {A = ‶ X} = s-var
s-refl {A = A `→ A₁} = s-arr s-refl s-refl
s-refl {A = `∀ A} = s-∀ s-refl

⊢to≤ : Γ ⊢ Σ ⇒ e ⇒ A
     → Γ ⊢ A ⌞ ≤⁺ ⌝ Σ ⊣ Γ ↪ A

subsumption : Γ ⊢ Σ ⇒ e ⇒ A
            → ⟦ Σ ⟧⇒⟦ e̅ , □ ⟧
            → e̅ ⊕ Σ'' := Σ'
            → Γ ⊢ A ⌞ ≤⁺ ⌝ Σ' ⊣ Δ ↪ A' -- Δ is Γ <--- only under some closeness conditions
            → Γ ⊢ Σ' ⇒ e ⇒ A'
-- corollary            
subsumption0 : Γ ⊢ □ ⇒ e ⇒ A
             → Γ ⊢ A ⌞ ≤⁺ ⌝ Σ ⊣ Δ ↪ A'
             → Γ ⊢ Σ ⇒ e ⇒ A'
subsumption0 ⊢e s = subsumption ⊢e none-□ ⊕nil s

{-
s-refined' : Γ ⊢ A ⌞ ≤⁺ ⌝ Σ ⊣ Γ ↪ B
           → Γ ⊢ B ⌞ ≤⁺ ⌝ Σ ⊣ Γ ↪ B
s-refined' s-int = s-int
s-refined' (s-empty clo) = s-empty clo
s-refined' s-var = s-var
s-refined' (s-ex-l^ x-in inst) = s-refl
s-refined' (s-ex-l= x-in s) = s-refl
s-refined' (s-ex-r= x-in s) = s-refl
s-refined' (s-arr s s₁) = s-refl
s-refined' (s-term-c ⊢e s) with ⊢id0 ⊢e
... | refl = s-term-c ⊢e (s-refined' s)
s-refined' (s-term-o opnA ⊢e s s₁) with ⊆-id (s-⊆ s) (s-⊆ s₁)
... | refl = s-term-c (subsumption0 ⊢e s-refl) (s-refined' s₁)
s-refined' (s-∀ s) = s-∀ (s-refined' s)
s-refined' (s-∀l s upᶜ upᵉ st₁ st₂) = {!!}
-}

s-refined-p : Γ ⊢ A ⌞ ≤ ⌝ Σ ⊣ Δ ↪ B
            → Polarity Γ A Σ ≤
            → Δ ⊢ B ⌞ ≤ ⌝ Σ ⊣ Δ ↪ B
s-refined-p s-int pr = s-int
s-refined-p (s-empty clo) pr = s-empty clo
s-refined-p s-var pr = s-refl
s-refined-p (s-ex-l^ x-in inst) pr = s-refl
s-refined-p (s-ex-l= x-in s) pr = s-refl
s-refined-p (s-ex-r^ x-in inst) pr = s-refl
s-refined-p (s-ex-r= x-in s) pr = s-refl
s-refined-p (s-arr s s₁) pr = s-refl
s-refined-p (s-term-c ⊢e s) (polar-r cloΓ (⊢c-term cloe cloΣ)) with ⊢id0 ⊢e
... | refl = s-term-c {!!} (s-refined-p s (polar-r cloΓ cloΣ))
s-refined-p (s-term-o opnA ⊢e s s₁) pr = {!!}
s-refined-p (s-∀ s) pr = s-∀ (s-refined-p s (polar-∀ pr))
s-refined-p (s-∀l s upᶜ upᵉ st₁ st₂) pr = {!s-refined-p s ?!}


s-refined : Γ ⊢ A ⌞ ≤⁺ ⌝ Σ ⊣ Δ ↪ B -- generlise output env to be Δ to deal with s-∀l case
          → Δ ⊢ B ⌞ ≤⁺ ⌝ Σ ⊣ Δ ↪ B
          
s-refined s-int = s-int
s-refined (s-empty clo) = s-empty clo
s-refined s-var = s-var
s-refined (s-ex-l^ x-in inst) = s-refl
s-refined (s-ex-l= x-in s) = s-refl
s-refined (s-ex-r= x-in s) = s-refl
s-refined (s-arr s s₁) = s-refl
s-refined (s-term-c ⊢e s) with ⊢id0 ⊢e
... | refl = s-term-c {!!} (s-refined s)
s-refined (s-term-o opnA ⊢e s s₁) = s-term-c {!subsumption0 ⊢e s-refl!} (s-refined s₁)
s-refined (s-∀ s) = s-∀ (s-refined s)
s-refined (s-∀l s upᶜ upᵉ st₁ st₂) = {!s-refined s!}

⊢to≤ (⊢lit cloΓ) = s-empty ⊢c-int
⊢to≤ (⊢var cloΓ x∈Γ) = s-empty (∋⦂-closed cloΓ x∈Γ)
⊢to≤ (⊢ann ⊢e) = s-empty (⊢close-τ ⊢e)
⊢to≤ (⊢app ⊢e) with ⊢to≤ ⊢e
... | s-term-c ⊢e₁ r = r
... | s-term-o opnA ⊢e₁ r r₁ with ⊆-id (s-⊆ r) (s-⊆ r₁)
... | refl = r₁
⊢to≤ (⊢lam₁ ⊢e) with ⊢id0 ⊢e
... | refl = s-refl
⊢to≤ (⊢lam₂ ⊢e up-c ⊢e₁) = s-term-c (subsumption0 ⊢e s-refl) (s-strengthen,0 (⊢to≤ ⊢e₁) up-c)
⊢to≤ (⊢sub ⊢e ne gc cloΣ s) = {!!}
⊢to≤ (⊢tabs ⊢e) = s-empty (⊢c-∀ (⊢closeA ⊢e))

subsumption ⊢e = {!!}





