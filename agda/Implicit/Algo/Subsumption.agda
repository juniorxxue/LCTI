module Implicit.Algo.Subsumption where

open import Implicit.Common
open import Implicit.Algo
open import Implicit.Algo.Postulates
open import Implicit.Algo.Properties
open import Implicit.Algo.Trans

s-refl : ∀ {Ψ : SEnv n m} {A}
  → Ψ ⊢ A ≤ τ A ⊣ Ψ ↪ A -- the output context shouldn't be affected
s-refl {A = Int} = s-int
s-refl {A = ‶ X} = s-var
s-refl {A = A `→ A₁} = s-arr (s-refl {A = A}) (s-refl {A = A₁})
s-refl {A = `∀ A} = s-∀ (s-refl {A = A})

m-w-eq : ∀ (Γ : Env n m)
  → 𝕄 (𝕎 Γ) ≡ Γ
m-w-eq ∅ = refl
m-w-eq (Γ , A) rewrite m-w-eq Γ = refl
m-w-eq (Γ ,∙) rewrite m-w-eq Γ = refl
m-w-eq (Γ ,= A) rewrite m-w-eq Γ = refl

⊢a-m-w : ∀ {Γ : Env n m} {Σ e A}
  → Γ ⊢ Σ ⇒ e ⇒ A
  → 𝕄 (𝕎 Γ) ⊢ Σ ⇒ e ⇒ A
⊢a-m-w {Γ = Γ} ⊢e rewrite m-w-eq Γ = ⊢e  

⊢to≤ : ∀ {Γ : Env n m} {e Σ A}
  → Γ ⊢ Σ ⇒ e ⇒ A
  → 𝕎 Γ ⊢ A ≤ Σ ⊣ 𝕎 Γ ↪ A

subsumption : ∀ {Γ : Env n m} {Σ Σ' Σ'' Ψ e A A' a̅}
  → Γ ⊢ Σ ⇒ e ⇒ A
  → ⟦ Σ ⟧⇒⟦ a̅ , □ ⟧
  → a̅ ⊕ Σ'' := Σ'
  → 𝕎 Γ ⊢ A ≤ Σ' ⊣ Ψ ↪ A'
  → Γ ⊢ Σ' ⇒ e ⇒ A'

subsumption0 : ∀ {Γ : Env n m} {Ψ Σ e A A'}
  → Γ ⊢ □ ⇒ e ⇒ A
  → 𝕎 Γ ⊢ A ≤ Σ ⊣ Ψ ↪ A'
  → Γ ⊢ Σ ⇒ e ⇒ A'
subsumption0 ⊢e s = subsumption ⊢e none-□ ⊕nil s

s-refined : ∀ {Ψ Ψ' : SEnv n m} {Σ A B}
  → Ψ ⊢ A ≤ Σ ⊣ Ψ' ↪ B
  → Ψ' ⊢ B ≤ Σ ⊣ Ψ' ↪ B

s-refined s-int = s-int
s-refined (s-empty p) = s-empty p
s-refined s-var = s-var
s-refined (s-ex-l^ clo x-in inst) = {!!}
s-refined s'@(s-ex-l= clo x-in s) = {!!}
s-refined (s-ex-r^ clo x-in inst) = {!!}
s-refined (s-ex-r= clo x-in s) = {!!}
s-refined (s-arr s s₁) = {!!}
s-refined (s-term-c cloA cloB ⊢e s) = s-term-c {!!} {!!} {!⊢id0-h ⊢e!} (s-refined s) -- easy
s-refined s'@(s-term-o op ⊢e s s₁) with ≤id0 s
... | refl = s-term-c {!!} {!!} {!!} (s-refined s₁)
s-refined (s-∀ s) = s-∀ (s-refined s)
s-refined (s-∀l-^ s) = {!s-refined s!}
s-refined (s-∀l-eq s st₁ st₂) = {!s-refined s!} -- substituition lemma

⊢to≤ ⊢lit = s-empty ⊢c-int
⊢to≤ ⊢e@(⊢var x∈Γ) = s-empty (⊢a→⊢c ⊢e)
⊢to≤ (⊢ann ⊢e) rewrite ⊢id0 ⊢e = s-empty (⊢a→⊢c ⊢e)
⊢to≤ (⊢app ⊢e) with ⊢to≤ ⊢e
... | s-term-c x x₁ x₂ r = r
... | s-term-o x x₁ r r₁ = s-closed-l r₁
⊢to≤ (⊢lam₁ ⊢e) with ⊢to≤ ⊢e
... | s rewrite ⊢id0 ⊢e = s-refl
⊢to≤ {Γ = Γ} (⊢lam₂ ⊢e ⊢e₁) = s-term-c (⊢a→⊢c ⊢e) (⊢a→⊢c-weaken ⊢e₁) (⊢a-m-w (subsumption0 {Ψ = 𝕎 Γ} ⊢e s-refl)) (s-strengthen0 (⊢to≤ ⊢e₁))
⊢to≤ (⊢sub ⊢e ne gc s) = s-refined s
⊢to≤ (⊢tabs ⊢e) = s-empty (⊢c-∀ (⊢a→⊢c ⊢e))

subsumption {Σ' = □} ⊢e none-□ ⊕nil (s-empty p) = ⊢e

subsumption {Σ' = τ _} ⊢lit spl ⊕nil s = ⊢sub ⊢lit ne-τ gc-i (s-closed-r s)
subsumption {Σ' = τ _} (⊢var x∈Γ) none-□ ⊕nil s = ⊢sub (⊢var x∈Γ) ne-τ gc-var (s-closed-r s)
subsumption {Σ' = τ _} (⊢ann ⊢e) none-□ ⊕nil s = ⊢sub (⊢ann ⊢e) ne-τ gc-ann (s-closed-r s)
subsumption {Σ' = τ _} (⊢app ⊢e) none-□ ⊕nil s with ⊢to≤ ⊢e
... | s-term-c cloA cloB ⊢e₁ s₁ = ⊢app (subsumption ⊢e (have-e none-□) (⊕cons-e ⊕nil) (s-term-c cloA cloB ⊢e₁ s))
... | s-term-o op ⊢e₁ s₁ s₂ = ⊥-elim (𝕎-open op)
subsumption {Σ' = τ _} (⊢lam₂ ⊢e ⊢e₁) (have-e spl) () s
subsumption {Σ' = τ _} (⊢sub ⊢e ne gc (s-empty p)) none-□ ⊕nil s = ⊢sub ⊢e ne-τ gc (s-closed-r s)
subsumption {Σ' = τ _} (⊢tabs ⊢e) none-□ ⊕nil s = ⊢sub (⊢tabs ⊢e) ne-τ gc-tlam (s-closed-r s)

subsumption {Σ' = [ e ]↝ Σ'} (⊢var x∈Γ) spl ch s = ⊢sub (⊢var x∈Γ) ne-app gc-var (s-closed-r s)
subsumption {Σ' = [ e ]↝ Σ'} (⊢ann ⊢e) spl ch s = ⊢sub (⊢ann ⊢e) ne-app gc-ann (s-closed-r s)
subsumption {Σ' = [ e ]↝ Σ'} (⊢app ⊢e) spl ch s with ⊢to≤ ⊢e
... | s-term-c cloA cloB ⊢e₁ s₁ = ⊢app (subsumption ⊢e (have-e spl) (⊕cons-e ch) (s-term-c cloA cloB ⊢e₁ s))
... | s-term-o op ⊢e₁ s₁ s₂ = ⊥-elim (𝕎-open op)
subsumption {Σ' = [ e ]↝ Σ'} (⊢lam₂ ⊢e ⊢e₁) (have-e spl) (⊕cons-e ch) (s-term-c cloA cloB ⊢e₂ s) rewrite ⊢id0 ⊢e₂ =
  ⊢lam₂ ⊢e (subsumption ⊢e₁ (Σsplit-weaken0 spl) (⊕-weaken0 ch) (s-weaken0 s))
subsumption {Σ' = [ e ]↝ Σ'} (⊢lam₂ ⊢e ⊢e₁) (have-e spl) (⊕cons-e ch) (s-term-o op ⊢e₂ s s₁) = ⊥-elim (𝕎-open op)
subsumption {Σ' = [ e ]↝ Σ'} (⊢sub ⊢e ne gc s₁) spl ch s = ⊢sub ⊢e ne-app gc (s-trans s₁ spl ch (s-closed-r s))
subsumption {Σ' = [ e ]↝ Σ'} (⊢tabs ⊢e) none-□ ch s = ⊢sub (⊢tabs ⊢e) ne-app gc-tlam (s-closed-r s)


