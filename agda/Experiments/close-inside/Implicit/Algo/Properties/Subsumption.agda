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
  s-trans : Γ ⊢ A₁ ⌞ ≤ ⌝ Σ ⊣ Δ ↪ A₂
        → Δ ⊢ A₂ ⌞ ≤ ⌝ Σ' ⊣ Δ ↪ A₃ -- A₂ couldn't be open
        → Σ ≊ Σ'
        → Γ ⊢ A₁ ⌞ ≤ ⌝ Σ' ⊣ Δ ↪ A₃

  s-subst : Γ ,= T ⊢ A ⌞ ≤ ⌝ Σ' ⊣ Δ ,= T ↪ B
          → ⟦ T ⟧ A ⇘ A*
          → ⟦ T ⟧ B ⇘ B*
          → ↑tyᶜ0 Σ ⇘ Σ'
          → Γ ⊢ A* ⌞ ≤ ⌝ Σ ⊣ Δ ↪ B*

s-refl : Γ ⊢ A ⌞ ≤ ⌝ τ A ⊣ Γ ↪ A
s-refl {A = Int} = s-int
s-refl {A = ‶ X} = s-var
s-refl {A = A `→ A₁} = s-arr s-refl s-refl
s-refl {A = `∀ A} = s-∀ s-refl

----------------------------------------------------------------------
--+                           Main Logic                           +--
----------------------------------------------------------------------

⊢to≤ : Γ ⊢ Σ ⇒ e ⇒ A
     → Γ ⊢ A ⌞ ≤⁺ ⌝ Σ ⊣ Γ ↪ A

subsumption : Γ ⊢ Σ ⇒ e ⇒ A
             → Σ ≊ Σ'
             → Γ ⊢cᶜ Σ'
             → Γ ⊢ A ⌞ ≤⁺ ⌝ Σ' ⊣ Γ ↪ A'
             → Γ ⊢ Σ' ⇒ e ⇒ A'

-- corollary
subsumption0 : Γ ⊢ □ ⇒ e ⇒ A
             → Γ ⊢ A ⌞ ≤⁺ ⌝ Σ ⊣ Γ ↪ A'
             → Γ ⊢cᶜ Σ
             → Γ ⊢ Σ ⇒ e ⇒ A'
subsumption0 ⊢e s clo = subsumption ⊢e ≊Z clo s

subsumption {Σ' = □} ⊢e ≊Z cloΣ' (s-empty clo) = ⊢e
subsumption {Σ' = τ _} (⊢lit cloΓ) ≊Z (⊢c-τ cloA) s = ⊢sub (⊢lit cloΓ) ne-τ gc-i (⊢c-τ cloA) s
subsumption {Σ' = τ _} (⊢var cloΓ x∈Γ) ≊Z (⊢c-τ cloA) s = ⊢sub (⊢var cloΓ x∈Γ) ne-τ gc-var (⊢c-τ cloA) s
subsumption {Σ' = τ _} (⊢ann ⊢e) ≊Z (⊢c-τ cloA) s = ⊢sub (⊢ann ⊢e) ne-τ gc-ann (⊢c-τ cloA) s
subsumption {Σ' = τ _} (⊢app ⊢e) ≊Z (⊢c-τ cloA) s with ⊢to≤ ⊢e
... | (s-term-c ⊢e₁ r) = ⊢app (subsumption ⊢e (≊S ≊Z) (⊢c-term (⊢closee ⊢e₁) (⊢c-τ cloA)) (s-term-c ⊢e₁ s))
... | s-term-o opnA ⊢e₁ r r₁ = ⊥-elim (⊢c-⊢o-disjoint (⊢closeA ⊢e₁) opnA)
subsumption {Σ' = τ _} (⊢tabs ⊢e) ≊Z (⊢c-τ cloA) s = ⊢sub (⊢tabs ⊢e) ne-τ gc-tlam (⊢c-τ cloA) s
subsumption {Σ' = [ e ]↝ Σ'} (⊢var cloΓ x∈Γ) newΣ cloΣ' s = ⊢sub (⊢var cloΓ x∈Γ) ne-app gc-var cloΣ' s
subsumption {Σ' = [ e ]↝ Σ'} (⊢ann ⊢e) newΣ cloΣ' s = ⊢sub (⊢ann ⊢e) ne-app gc-ann cloΣ' s
subsumption {Σ' = [ e ]↝ Σ'} (⊢app ⊢e) newΣ cloΣ' s with ⊢to≤ ⊢e
... | s-term-c ⊢e₁ r = ⊢app (subsumption ⊢e (≊S newΣ) (⊢c-term (⊢closee ⊢e₁) cloΣ') (s-term-c ⊢e₁ s))
... | s-term-o opnA ⊢e₁ r r₁ = ⊥-elim (⊢c-⊢o-disjoint (⊢closeA ⊢e₁) opnA)
subsumption {Σ' = [ e ]↝ Σ'} (⊢lam₂ ⊢e up-c ⊢e₁) (≊S newΣ) (⊢c-term cloe cloΣ') (s-term-c ⊢e₂ s) with ⊢id0 ⊢e₂
                                                                                                    | ↑tmᶜ0-total Σ'
... | refl | ⟨ nΣ' , up-Σ ⟩ = ⊢lam₂ ⊢e up-Σ (subsumption ⊢e₁
                                                         (≊-weaken newΣ up-c up-Σ)
                                                         (⊢cᶜ-weaken,0 cloΣ' up-Σ)
                                                         (s-weaken,0 s up-Σ))
subsumption {Σ' = [ e ]↝ Σ'} (⊢lam₂ ⊢e up-c ⊢e₁) (≊S newΣ) cloΣ' (s-term-o opnA ⊢e₂ s s₁)
  = ⊥-elim (⊢c-⊢o-disjoint (⊢closeA ⊢e) opnA)
subsumption {Σ' = [ e ]↝ Σ'} (⊢sub ⊢e ne gc cloΣ s₁) (≊S newΣ) (⊢c-term cloe cloΣ') s =
  ⊢sub ⊢e ne-app gc (⊢c-term cloe cloΣ') (s-trans s₁ s (≊S newΣ))
subsumption {Σ' = [ e ]↝ Σ'} (⊢tabs ⊢e) newΣ cloΣ' s = ⊢sub (⊢tabs ⊢e) ne-app gc-tlam cloΣ' s

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
... | refl = s-term-c (t-⊆-prv ⊢e (s-⊆ s) (s-closed-env s (polar-r cloΓ cloΣ))) (s-refined-p s (polar-r cloΓ cloΣ))
s-refined-p s'@(s-term-o opnA ⊢e s s₁) pr'@(polar-r cloΓ (⊢c-term cloe cloΣ)) =
  s-term-c (t-⊆-prv (subsumption0 ⊢e s-refl (⊢c-τ (⊢closeA ⊢e))) (s-⊆ s') (s-closed-env s' pr'))
           (s-refined-p s₁ (polar-r (s-closed-env s (polar-l cloΓ (⊢closeA ⊢e))) (⊆-cloAᶜ cloΣ (s-⊆ s))))
s-refined-p (s-∀ s) pr = s-∀ (s-refined-p s (polar-∀ pr))
s-refined-p (s-∀l s upᶜ upᵉ st₁ st₂) (polar-r cloΓ cloΣ) =
  s-subst (s-refined-p s (polar-r (clo-S^ cloΓ) (⊢cᶜ-weaken^0 cloΣ (↑tyᶜ-e upᵉ upᶜ))))
          (st-arr st₁ st₂) (st-arr st₁ st₂) (↑tyᶜ-e upᵉ upᶜ)

{-
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
s-refined (s-∀l s upᶜ upᵉ st₁ st₂) = {!s-refined-p s ?!}
-}

⊢to≤ (⊢lit cloΓ) = s-empty ⊢c-int
⊢to≤ (⊢var cloΓ x∈Γ) = s-empty (∋⦂-closed cloΓ x∈Γ)
⊢to≤ (⊢ann ⊢e) = s-empty (⊢close-τ ⊢e)
⊢to≤ (⊢app ⊢e) with ⊢to≤ ⊢e
... | s-term-c ⊢e₁ r = r
... | s-term-o opnA ⊢e₁ r r₁ with ⊆-id (s-⊆ r) (s-⊆ r₁)
... | refl = r₁
⊢to≤ (⊢lam₁ ⊢e) with ⊢id0 ⊢e
... | refl = s-refl
⊢to≤ (⊢lam₂ ⊢e up-c ⊢e₁) = s-term-c (subsumption0 ⊢e s-refl (⊢c-τ (⊢closeA ⊢e))) (s-strengthen,0 (⊢to≤ ⊢e₁) up-c)
⊢to≤ (⊢sub ⊢e ne gc cloΣ s) = s-refined-p s (polar-r (⊢closeΓ ⊢e) cloΣ)
⊢to≤ (⊢tabs ⊢e) = s-empty (⊢c-∀ (⊢closeA ⊢e))
