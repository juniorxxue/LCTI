module Implicit.Algo.Properties.Subsumption where

open import Implicit.Language.All
open import Implicit.Algo.Base
open import Implicit.Algo.Properties.Id
open import Implicit.Algo.Properties.Reflexivity
open import Implicit.Algo.Properties.Extension
open import Implicit.Algo.Properties.Regularity
open import Implicit.Algo.Properties.Polarity


postulate
  t-irrev-⊆ : 𝕣 Γ ⊢ Σ ⇒ e ⇒ A
            → Γ ⊆ Δ
            → 𝕣 Δ ⊢ Σ ⇒ e ⇒ A

⊢to≤ : Γ ⊢ Σ ⇒ e ⇒ A
     → Γ ⋈ ⊢ A ≤⁺ Σ ⊣ Γ ⋈ ↪ A

subsumption :  Γ ⊢ Σ ⇒ e ⇒ A
             → Σ ≊ Σ'
             → Γ ⋈ ⊢ A ≤⁺ Σ' ⊣ Γ ⋈ ↪ A'
             → Γ ⊢ Σ' ⇒ e ⇒ A'

subsumption0 : Γ ⊢ □ ⇒ e ⇒ A
             → Γ ⊢ τ A ⇒ e ⇒ A
subsumption0 ⊢e = subsumption ⊢e ≊Z (s-type (s-refl (reg-Z (t-env ⊢e)) (⊢r-weaken⋈0 (t-⊢r ⊢e))))


s-refined-p : Γ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B
            → Δ ⊢ B ≤⁺ Σ ⊣ Δ ↪ B
s-refined-p (s-empty cloΓ cloA x) = let regB = (⊢c-≫-⊢r cloΓ cloA x) in s-empty cloΓ (⊢r-⊢c regB ) (⊢r-≫-eq regB)
s-refined-p (s-type ss) = s-type (s-refl (ss-env-out ss) (ss-polarity+-out ss))
s-refined-p (s-term-c cloA ap ⊢e s) with ⊢id0 ⊢e
... | refl = let regA = ⊆-⊢r (⊢c-≫-⊢r (s-env-in s) cloA ap) (s-⊆ s)
             in s-term-c (⊢r-⊢c regA) (⊢r-≫-eq regA) (t-irrev-⊆ ⊢e (s-⊆ s)) (s-refined-p s)
s-refined-p s'@(s-term-o opnA ⊢e ss s) with subsumption0 ⊢e
... | ih = let regA = ⊆-⊢r (ss-polarity- ss) (s-⊆ s')
         in s-term-c (⊢r-⊢c regA) (⊢r-≫-eq regA) (t-irrev-⊆ ih (s-⊆ s')) (s-refined-p s)
s-refined-p (s-∀l s upᶜ upᵉ upC upD) = {!s-refined-p s!}

⊢to≤ (⊢lit regΓ) = s-empty (reg-Z regΓ) ⊢c-int grd-int
⊢to≤ (⊢var cloΓ x∈Γ) = s-empty (reg-Z cloΓ) {!!} {!!}
⊢to≤ (⊢ann ⊢e) = s-empty {!!} {!!} {!!}
⊢to≤ (⊢app ⊢e) with ⊢to≤ ⊢e
... | s-term-c cloA ap ⊢e₁ r = r
... | s-term-o opnA ⊢e₁ x r = ⊥-elim {!!}
⊢to≤ (⊢lam₁ ⊢e) = {!!}
⊢to≤ (⊢lam₂ ⊢e up-c ⊢e₁) = s-term-c {!!} {!!} {!!} {!!}
⊢to≤ (⊢sub ⊢e ne gc s) = s-refined-p s
⊢to≤ (⊢tabs ⊢e) = {!!}

subsumption {Σ' = τ A} (⊢lit regΓ) ≊Z s = ⊢sub (⊢lit regΓ) ne-τ gc-i s
subsumption {Σ' = τ A} (⊢var cloΓ x∈Γ) ≊Z s = ⊢sub (⊢var cloΓ x∈Γ) ne-τ gc-var s
subsumption {Σ' = τ A} (⊢ann ⊢e) ≊Z s = ⊢sub (⊢ann ⊢e) ne-τ gc-ann s
subsumption {Σ' = τ A} (⊢app ⊢e) ≊Z s with ⊢to≤ ⊢e
... | s-term-c cloA ap ⊢e₁ s₁ = ⊢app (subsumption ⊢e (≊S ≊Z) (s-term-c cloA ap ⊢e₁ s))
... | s-term-o opnA ⊢e₁ x s₁ = ⊥-elim {!!}
subsumption {Σ' = τ A} (⊢tabs ⊢e) ≊Z s = ⊢sub (⊢tabs ⊢e) ne-τ gc-tlam s
subsumption {Σ' = [ e ]↝ Σ'} (⊢app ⊢e) (≊S newΣ) s with ⊢to≤ ⊢e
... | s-term-c cloA ap ⊢e₁ r = ⊢app (subsumption ⊢e (≊S (≊S newΣ)) (s-term-c cloA ap ⊢e₁ s))
... | s-term-o opnA ⊢e₁ x r = ⊥-elim {!!}
subsumption {Σ' = [ e ]↝ Σ'} (⊢lam₂ ⊢e up-c ⊢e₁) (≊S newΣ) (s-term-c cloA ap ⊢e₂ s) = ⊢lam₂ {!!} {!!} (subsumption {!⊢e₁!} {!!} {!!})
subsumption {Σ' = [ e ]↝ Σ'} (⊢lam₂ ⊢e up-c ⊢e₁) (≊S newΣ) (s-term-o opnA ⊢e₂ x s) = ⊥-elim {!!}
subsumption {Σ' = [ e ]↝ Σ'} (⊢sub ⊢e ne gc s₁) (≊S newΣ) s = ⊢sub ⊢e ne-app gc {!!}
