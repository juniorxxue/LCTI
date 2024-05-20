module Poly.Complete where

open import Poly.Common
open import Poly.Decl
open import Poly.Algo
open import Poly.Algo.Subsumption

infix 3 _⊢_~_

data _⊢_~_ : Env n m → Counter × Type m → Context n m → Set

data _⊢_~_ where

  ~Z : ∀ {Γ : Env n m} {A}
    → Γ ⊢ ⟨ Z , A ⟩ ~ □

  ~∞ : ∀ {Γ : Env n m} {A }
    → Γ ⊢ ⟨ ∞ , A ⟩ ~ τ A

  ~S : ∀ {Γ : Env n m} {j A B Σ e}
    → (⊢e : Γ ⊢ □ ⇒ e ⇒ A)
    → Γ ⊢ ⟨ j , B ⟩ ~ Σ
    → Γ ⊢ ⟨ S j , A `→ B ⟩ ~ ([ e ]↝ Σ)

  ~Sτ : ∀ {Γ : Env n m} {j A B Σ}
    → Γ ⊢ ⟨ j , B ⟩ ~ Σ
    → Γ ⊢ ⟨ Sτ j , B ⟩ ~ (⟦ A ⟧↝ Σ)


postulate
  ~weaken0 : ∀ {Γ : Env n m} {Σ A B j}
    → Γ ⊢ ⟨ j , B ⟩ ~ Σ
    → Γ , A ⊢ ⟨ j , B ⟩ ~ ↑Σ0 Σ

  ⊢-to-⊢c : ∀ {Γ : Env n m} {Σ e A}
    → Γ ⊢ Σ ⇒ e ⇒ A
    → 𝕓 Γ ⊢c A

complete : ∀ {Γ : Env n m} {Σ j e A}
  → Γ ⊢ j # e ⦂ A
  → Γ ⊢ ⟨ j , A ⟩ ~ Σ
  → Γ ⊢ Σ ⇒ e ⇒ A

complete-≤ : ∀ {Γ : Env n m} {Σ j A B}
  → Γ ⊢ j # B ≤ A
  → Γ ⊢ ⟨ j , A ⟩ ~ Σ
  → 𝕓 Γ ⊢ B ≤ Σ ⊣ 𝕓 Γ ↪ A -- too strict
  
complete-inf : ∀ {Γ : Env n m} {e A}
  → Γ ⊢ Z # e ⦂ A
  → Γ ⊢ □ ⇒ e ⇒ A
complete-inf ⊢e = complete ⊢e ~Z  

complete-chk : ∀ {Γ : Env n m} {e A}
  → Γ ⊢ ∞ # e ⦂ A
  → Γ ⊢ τ A ⇒ e ⇒ A
complete-chk ⊢e = complete ⊢e ~∞

complete-≤-chk : ∀ {Γ : Env n m} {A B}
  → Γ ⊢ ∞ # B ≤ A
  → 𝕓 Γ ⊢ B ≤ τ A ⊣ 𝕓 Γ ↪ A
complete-≤-chk B≤A = complete-≤ B≤A ~∞  

complete ⊢lit ~Z = ⊢lit
complete (⊢var x) ~Z = ⊢var x
complete (⊢ann ⊢e) ~Z = ⊢ann (complete-chk ⊢e)
complete (⊢lam₁ ⊢e) ~∞ = ⊢lam₁ (complete-chk ⊢e)
complete (⊢lam₂ ⊢e) (~S ⊢e' j~Σ) = ⊢lam₂ ⊢e' (complete ⊢e (~weaken0 j~Σ))
complete (⊢app₁ ⊢e ⊢e₁) j~Σ = ⊢app (subsumption0 (complete-inf ⊢e) (s-term-c {!!} {!!} (complete-chk ⊢e₁) {!!})) -- more thinking needed
-- maybe some property like checking rule in previous system could be generlised
complete (⊢app₂ ⊢e ⊢e₁) j~Σ = ⊢app (complete ⊢e (~S (complete-inf ⊢e₁) j~Σ))
complete (⊢sub ⊢e B≤A j≢Z) j~Σ = subsumption0 (complete-inf ⊢e) (complete-≤ B≤A j~Σ)
complete (⊢tabs₁ ⊢e) ~Z = ⊢tabs₁ (complete-inf ⊢e)
complete (⊢tapp ⊢e) j~Σ = ⊢tapp (complete ⊢e (~Sτ j~Σ))

complete-≤ (s-refl ap) ~Z = s-empty {!!} {!!} -- easy
complete-≤ s-int ~∞ = s-int
complete-≤ s-var ~∞ = s-var
complete-≤ (s-arr₁ s s₁) ~∞ = s-arr (complete-≤-chk s) (complete-≤-chk s₁)
complete-≤ (s-arr₂ s s₁) (~S ⊢e j~Σ) = {!!}
complete-≤ (s-∀ s) j~Σ = {!!}
complete-≤ (s-∀l s x) j~Σ = {!!}
complete-≤ (s-∀lτ s) (~Sτ j~Σ) = {!!}
complete-≤ (s-var-l x s) ~∞ = s-ex-l= {!!} {!!} (complete-≤-chk s) -- ok
complete-≤ (s-var-r x s) ~∞ = s-ex-r= {!!} {!!} (complete-≤-chk s) -- ok
