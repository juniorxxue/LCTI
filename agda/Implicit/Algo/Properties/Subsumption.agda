module Implicit.Algo.Properties.Subsumption where

open import Implicit.Language
open import Implicit.Algo.Base
open import Implicit.Algo.Properties.Id
-- open import Implicit.Algo.Properties.OpenClose
open import Implicit.Algo.Properties.Extension

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

s-refined : Γ ⊢ A ⌞ ≤⁺ ⌝ Σ ⊣ Δ ↪ B
          → Δ ⊢ B ⌞ ≤⁺ ⌝ Σ ⊣ Δ ↪ B
          
s-refined s-int = s-int
s-refined (s-empty clo) = s-empty clo
s-refined s-var = s-var
s-refined (s-ex-l^ x-in inst) = s-refl
s-refined (s-ex-l= x-in s) = s-refl
s-refined (s-ex-r= x-in s) = s-refl
s-refined (s-arr s s₁) = s-refl
s-refined (s-term-c ⊢e s) = s-term-c {!!} (s-refined s)
s-refined (s-term-o opnA ⊢e s s₁) = s-term-c {!!} (s-refined s₁)
s-refined (s-∀ s) = s-∀ (s-refined s)
s-refined (s-∀l s upᶜ upᵉ st₁ st₂) = {!s-refined s!}

⊢to≤ ⊢e = {!!}

subsumption ⊢e = {!!}





