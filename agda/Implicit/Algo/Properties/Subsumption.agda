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
s-refined s-empty = s-empty
s-refined s-var = s-var
s-refined (s-ex-l^ x-in inst) = s-refl
s-refined (s-ex-l= x-in s) = s-refl
s-refined (s-ex-r= x-in s) = s-refl
s-refined (s-arr s s₁) = s-refl
s-refined (s-term-c ⊢e s) = s-term-c {!!} (s-refined s)
s-refined (s-term-o opnA ⊢e s s₁) = s-term-c {!!} (s-refined s₁)
s-refined (s-∀ s) = s-∀ (s-refined s)
s-refined (s-∀l s upᶜ upᵉ st₁ st₂) = {!s-refined s!}

⊢to≤ ⊢lit = {!!}
⊢to≤ (⊢var x∈Γ) = {!!}
⊢to≤ (⊢ann ⊢e) = {!!}
⊢to≤ (⊢app ⊢e) with ⊢to≤ ⊢e
... | s-term-c ⊢e₁ s = s
... | s-term-o opnA ⊢e₁ s s₁ = {!!}
⊢to≤ (⊢lam₁ ⊢e) = {!!}
⊢to≤ (⊢lam₂ ⊢e up-c ⊢e₁) = s-term-c {!!} {!⊢to≤ ⊢e₁!} -- ok
⊢to≤ (⊢sub ⊢e ne gc s) = {!!}
⊢to≤ (⊢tabs ⊢e) = {!!}

subsumption {Σ' = □} ⊢e none-□ ⊕nil s-empty = ⊢e

subsumption {Σ' = τ _} ⊢lit spl ⊕nil s = ⊢sub ⊢lit ne-τ gc-i {!!}
subsumption {Σ' = τ _} (⊢var x∈Γ) none-□ ⊕nil s = ⊢sub (⊢var x∈Γ) ne-τ gc-var {!!}
subsumption {Σ' = τ _} (⊢ann ⊢e) none-□ ⊕nil s = ⊢sub (⊢ann ⊢e) ne-τ gc-ann {!!}
subsumption {Σ' = τ _} (⊢app ⊢e) none-□ ⊕nil s with ⊢to≤ ⊢e
... | s-term-c ⊢e₁ s₁ = ⊢app (subsumption ⊢e (have-e none-□) (⊕cons-e ⊕nil) (s-term-c ⊢e₁ s))
... | s-term-o op ⊢e₁ s₁ s₂ = {!!}
subsumption {Σ' = τ _} (⊢lam₂ ⊢e up-c ⊢e₁) (have-e spl) () s
subsumption {Σ' = τ _} (⊢sub ⊢e ne gc s-empty) none-□ ⊕nil s = ⊢sub ⊢e ne-τ gc {!!}
subsumption {Σ' = τ _} (⊢tabs ⊢e) none-□ ⊕nil s = ⊢sub (⊢tabs ⊢e) ne-τ gc-tlam {!!}

subsumption {Σ' = [ e ]↝ Σ'} (⊢var x∈Γ) spl ch s = ⊢sub (⊢var x∈Γ) ne-app gc-var {!!}
subsumption {Σ' = [ e ]↝ Σ'} (⊢ann ⊢e) spl ch s = ⊢sub (⊢ann ⊢e) ne-app gc-ann {!!}
subsumption {Σ' = [ e ]↝ Σ'} (⊢app ⊢e) spl ch s = {!⊢to≤ ⊢e!}

{- with ⊢to≤ ⊢e
... | s-term-c ⊢e₁ s₁ = ⊢app (subsumption ⊢e (have-e spl) (⊕cons-e ch) (s-term-c ⊢e₁ s))
... | s-term-o op ⊢e₁ s₁ s₂ = {!!}
-}
subsumption {Σ' = [ e ]↝ Σ'} (⊢lam₂ ⊢e up-c ⊢e₁) (have-e spl) (⊕cons-e ch) (s-term-c ⊢e₂ s) rewrite ⊢id0 ⊢e₂ =
  ⊢lam₂ ⊢e {!!} (subsumption ⊢e₁ {!!} {!!} {!!})
subsumption {Σ' = [ e ]↝ Σ'} (⊢lam₂ ⊢e up-c ⊢e₁) (have-e spl) (⊕cons-e ch) (s-term-o op ⊢e₂ s s₁) = {!!}
subsumption {Σ' = [ e ]↝ Σ'} (⊢sub ⊢e ne gc s₁) spl ch s = ⊢sub ⊢e ne-app gc {!!}
subsumption {Σ' = [ e ]↝ Σ'} (⊢tabs ⊢e) none-□ ch s = ⊢sub (⊢tabs ⊢e) ne-app gc-tlam {!!}





