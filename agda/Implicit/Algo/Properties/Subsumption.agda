module Implicit.Algo.Properties.Subsumption where

open import Implicit.Language
open import Implicit.Algo.Base
open import Implicit.Algo.Properties.Id
open import Implicit.Algo.Properties.OpenClose
open import Implicit.Algo.Properties.Extension

postulate
  inf-unique : ∀ {Γ : Env n m} {e A₁ A₂}
    → Γ ⊢ □ ⇒ e ⇒ A₁
    → Γ ⊢ □ ⇒ e ⇒ A₂
    → A₁ ≡ A₂

  ⊢a-m-w' : ∀ {Γ : Env n m} {Σ e A}
    → 𝕄 (𝕎 Γ) ⊢ Σ ⇒ e ⇒ A
    → Γ ⊢ Σ ⇒ e ⇒ A

s⁺-refl : ∀ {Ψ : SEnv n m} {A}
  → Ψ ⊢c A
  → Ψ ⊢ A ≤⁺ τ A ⊣ Ψ ↪ A -- the output context shouldn't be affected  
s⁻-refl : ∀ {Ψ : SEnv n m} {A}
  → Ψ ⊢c A
  → Ψ ⊢ A ≤⁻ τ A ⊣ Ψ ↪ A
  
s⁺-refl ⊢c-int = s⁺-int
s⁺-refl (⊢c-var-∙ x) = s⁺-var (⊢c-var-∙ x)
s⁺-refl (⊢c-var-= x) = s⁺-var (⊢c-var-= x)
s⁺-refl (⊢c-arr cloA cloA₁) = s⁺-arr cloA cloA₁ (s⁻-refl cloA) (s⁺-refl cloA₁)
s⁺-refl (⊢c-∀ cloA) = s⁺-∀ (⊢c-∀ cloA) (s⁺-refl cloA)

s⁻-refl ⊢c-int = s⁻-int
s⁻-refl (⊢c-var-∙ x) = s⁻-var (⊢c-var-∙ x)
s⁻-refl (⊢c-var-= x) = s⁻-var (⊢c-var-= x)
s⁻-refl (⊢c-arr cloA cloA₁) = s⁻-arr cloA cloA₁ (s⁺-refl cloA) (s⁻-refl cloA₁)
s⁻-refl (⊢c-∀ cloA) = s⁻-∀ (⊢c-∀ cloA) (s⁻-refl cloA)
  
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
  → 𝕎 Γ ⊢ A ≤⁺ Σ ⊣ 𝕎 Γ ↪ A

subsumption : ∀ {Γ : Env n m} {Σ Σ' Σ'' Ψ e A A' a̅}
  → Γ ⊢ Σ ⇒ e ⇒ A
  → ⟦ Σ ⟧⇒⟦ a̅ , □ ⟧
  → a̅ ⊕ Σ'' := Σ'
  → 𝕎 Γ ⊢ A ≤⁺ Σ' ⊣ Ψ ↪ A'
  → Γ ⊢ Σ' ⇒ e ⇒ A'

subsumption0 : ∀ {Γ : Env n m} {Ψ Σ e A A'}
  → Γ ⊢ □ ⇒ e ⇒ A
  → 𝕎 Γ ⊢ A ≤⁺ Σ ⊣ Ψ ↪ A'
  → Γ ⊢ Σ ⇒ e ⇒ A'
subsumption0 ⊢e s = subsumption ⊢e none-□ ⊕nil s

s-refined-c : ∀ {Ψ Ψ' : SEnv n m} {Σ A B}
  → Ψ ⊢ A ≤⁺ Σ ⊣ Ψ' ↪ B
  → Ψ ⊢c A
  → Ψ ⊢cᶜ Σ
  → Ψ' ⊢ B ≤⁺ Σ ⊣ Ψ' ↪ B
s-refined-c s = {!!}

s-refined : ∀ {Ψ Ψ' : SEnv n m} {Σ A B}
  → Ψ ⊢ A ≤⁺ Σ ⊣ Ψ' ↪ B
  → Ψ' ⊢ B ≤⁺ Σ ⊣ Ψ' ↪ B
s-refined s⁺-int = s⁺-int
s-refined (s⁺-empty cloA) = s⁺-empty cloA
s-refined (s⁺-var cloX) = s⁺-var cloX
s-refined (s⁺-ex-l^ cloA x-in inst) = s⁺-refl {!!}
s-refined (s⁺-ex-l= cloA x-in s) = s⁺-refl {!!}
s-refined (s⁺-ex-r= cloA x-in s) = {!!}
s-refined (s⁺-arr cloC cloD s s₁) = s⁺-refl {!!}
s-refined (s⁺-term-c cloA cloΣ ⊢e s) = {!!}
s-refined (s⁺-term-o opnA cloΣ ⊢e s s₁) = {!!}
s-refined (s⁺-∀ cloB s) = s⁺-∀ {!!} (s-refined s)
s-refined (s⁺-∀l cloΣ s upᶜ upᵉ st₁ st₂) = {!s-refined s!}

{-
s-refined s-int = s-int
s-refined (s-empty p) = s-empty p
s-refined (s-var is∙) = s-var is∙
s-refined (s-ex-l^ clo x-in inst) = s-refl {!!}
s-refined s'@(s-ex-l= clo x-in s) = s-refl {!!}
s-refined (s-ex-r^ clo x-in inst) = s-refl {!!}
s-refined (s-ex-r= clo x-in s) = s-refl {!!}
s-refined (s-arr s s₁) = {!!}
s-refined (s-term-c cloA ⊢e s) = s-term-c {!!} {!⊢id0-h ⊢e!} (s-refined s) -- easy
s-refined s'@(s-term-o op ⊢e s s₁) with ≤id0 s
... | refl = s-term-c {!!} (subsumption0 {!!} {!!}) (s-refined s₁)
s-refined (s-∀ s) = s-∀ (s-refined s)
s-refined (s-∀l s upc upe st₁ st₂) = {!s-refined s!} -- substituition lemma

⊢to≤ ⊢lit = s-empty ⊢c-int
⊢to≤ ⊢e@(⊢var x∈Γ) = s-empty (⊢a→⊢c ⊢e)
⊢to≤ (⊢ann ⊢e) rewrite ⊢id0 ⊢e = s-empty (⊢a→⊢c ⊢e)
⊢to≤ (⊢app ⊢e) with ⊢to≤ ⊢e
... | s-term-c x x₂ r = r
... | s-term-o op x r r₁ = {!!}
⊢to≤ (⊢lam₁ ⊢e) with ⊢to≤ ⊢e
... | s rewrite ⊢id0 ⊢e = {!!}
⊢to≤ {Γ = Γ} (⊢lam₂ ⊢e up-c ⊢e₁) = s-term-c (⊢a→⊢c ⊢e) (⊢a-m-w (subsumption0 {Ψ = 𝕎 Γ} ⊢e {!!})) {!!}
⊢to≤ (⊢sub ⊢e ne gc s) = {!!}
-- s-refined s
⊢to≤ (⊢tabs ⊢e) = s-empty (⊢c-∀ (⊢a→⊢c ⊢e))

subsumption {Σ' = □} ⊢e none-□ ⊕nil (s-empty p) = ⊢e

subsumption {Σ' = τ _} ⊢lit spl ⊕nil s = ⊢sub ⊢lit ne-τ gc-i (s-closed-r s)
subsumption {Σ' = τ _} (⊢var x∈Γ) none-□ ⊕nil s = ⊢sub (⊢var x∈Γ) ne-τ gc-var (s-closed-r s)
subsumption {Σ' = τ _} (⊢ann ⊢e) none-□ ⊕nil s = ⊢sub (⊢ann ⊢e) ne-τ gc-ann (s-closed-r s)
subsumption {Σ' = τ _} (⊢app ⊢e) none-□ ⊕nil s with ⊢to≤ ⊢e
... | s-term-c cloA ⊢e₁ s₁ = ⊢app (subsumption ⊢e (have-e none-□) (⊕cons-e ⊕nil) (s-term-c cloA ⊢e₁ s))
... | s-term-o op ⊢e₁ s₁ s₂ = {!!}
subsumption {Σ' = τ _} (⊢lam₂ ⊢e up-c ⊢e₁) (have-e spl) () s
subsumption {Σ' = τ _} (⊢sub ⊢e ne gc (s-empty p)) none-□ ⊕nil s = ⊢sub ⊢e ne-τ gc (s-closed-r s)
subsumption {Σ' = τ _} (⊢tabs ⊢e) none-□ ⊕nil s = ⊢sub (⊢tabs ⊢e) ne-τ gc-tlam (s-closed-r s)

subsumption {Σ' = [ e ]↝ Σ'} (⊢var x∈Γ) spl ch s = ⊢sub (⊢var x∈Γ) ne-app gc-var (s-closed-r s)
subsumption {Σ' = [ e ]↝ Σ'} (⊢ann ⊢e) spl ch s = ⊢sub (⊢ann ⊢e) ne-app gc-ann (s-closed-r s)
subsumption {Σ' = [ e ]↝ Σ'} (⊢app ⊢e) spl ch s with ⊢to≤ ⊢e
... | s-term-c cloA ⊢e₁ s₁ = ⊢app (subsumption ⊢e (have-e spl) (⊕cons-e ch) (s-term-c cloA ⊢e₁ s))
... | s-term-o op ⊢e₁ s₁ s₂ = {!!}
subsumption {Σ' = [ e ]↝ Σ'} (⊢lam₂ ⊢e up-c ⊢e₁) (have-e spl) (⊕cons-e ch) (s-term-c cloA ⊢e₂ s) rewrite ⊢id0 ⊢e₂ =
  ⊢lam₂ ⊢e {!!} (subsumption ⊢e₁ {!!} {!!} {!!})
subsumption {Σ' = [ e ]↝ Σ'} (⊢lam₂ ⊢e up-c ⊢e₁) (have-e spl) (⊕cons-e ch) (s-term-o op ⊢e₂ s s₁) rewrite inf-unique ⊢e (⊢a-m-w' ⊢e₂) =
  ⊢lam₂ (⊢a-m-w' ⊢e₂) {!!} (subsumption ⊢e₁ {!!} {!!} {!s-weaken0 s₁!})
subsumption {Σ' = [ e ]↝ Σ'} (⊢sub ⊢e ne gc s₁) spl ch s = ⊢sub ⊢e ne-app gc {!!}
subsumption {Σ' = [ e ]↝ Σ'} (⊢tabs ⊢e) none-□ ch s = ⊢sub (⊢tabs ⊢e) ne-app gc-tlam (s-closed-r s)
-}


