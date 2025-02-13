module Implicit.CompleteDeclAlgo where

open import Implicit.Language.All hiding (_≤_)
open import Implicit.Decl.All
open import Implicit.Algo.All

infix 3 _⊢_~_
data _⊢_~_ : Env n m → Counter × Type m → Context n m → Set where

  ~Z : ∀ {Γ : Env n m} {A}
    → Γ ⊢ ⟨ Z , A ⟩ ~ □

  ~∞ : ∀ {Γ : Env n m} {A }
    → Γ ⊢ ⟨ ∞ , A ⟩ ~ τ A

  ~I : ∀ {Γ : Env n m} {j A B Σ e}
    → (⊢e : Γ ⊢ □ ⇒ e ⇒ A)
    → Γ ⊢ ⟨ j , B ⟩ ~ Σ
    → Γ ⊢ ⟨ 𝕚 j , A `→ B ⟩ ~ ([ e ]↝ Σ)

  ~C : ∀ {Γ : Env n m} {j A B Σ e}
    → (⊢e : Γ ⊢ τ A ⇒ e ⇒ A)
    → Γ ⊢ ⟨ j , B ⟩ ~ Σ
    → Γ ⊢ ⟨ 𝕔 j , A `→ B ⟩ ~ ([ e ]↝ Σ)

postulate
  ~weaken,0 : Γ ⊢ ⟨ j , B ⟩ ~ Σ
            → ↑tmᶜ0 Σ ⇘ Σ'
            → Γ , A ⊢ ⟨ j , B ⟩ ~ Σ'

  sub-gen :
      Γ ⊢ □ ⇒ e ⇒ A
    → (ne : NonEmpty Σ)
    → (cloΣ : Γ ⊢cᶜ Σ)
    → (s : Γ ⊢ A ⌞ ≤⁺ ⌝ Σ ⊣ Γ ↪ B)
    → Γ ⊢ Σ ⇒ e ⇒ B




complete-≤ : Γ ⊢ j # A ≤ B
           → Γ ⊢ ⟨ j , B ⟩ ~ Σ
           → Γ ⊢ A ⌞ ≤⁺ ⌝ Σ ⊣ Γ ↪ B
complete-≤ (s-refl cloΓ cloA) ~Z = {!!}
complete-≤ (s-int cloΓ) j~Σ = {!!}
complete-≤ (s-var-∙ cloΓ inΓ) j~Σ = {!!}
complete-≤ (s-arr₁ s s₁) j~Σ = {!!}
complete-≤ (s-arr₂ s s₁) j~Σ = {!!}
complete-≤ (s-arr₃ cloA s) j~Σ = {!!}
complete-≤ (s-∀ s) j~Σ = {!!}
complete-≤ (s-∀l x s ic fd) j~Σ = {!!}

complete : Γ ⊢ j # e ⦂ A
         → Γ ⊢ ⟨ j , A ⟩ ~ Σ
         → Γ ⊢ Σ ⇒ e ⇒ A

complete (⊢lit cloΣ) ~Z = {!!}
complete (⊢var cloΣ x∈Γ) ~Z = {!!}
complete (⊢ann ⊢e) ~Z = ⊢ann (complete ⊢e ~∞)
complete (⊢lam₁ ⊢e) ~∞ = ⊢lam₁ (complete ⊢e ~∞)
complete (⊢lam₂ ⊢e) (~I ⊢e₁ j~Σ) with complete ⊢e (~weaken,0 j~Σ {!!})
... | r = ⊢lam₂ ⊢e₁ {!!} r
complete (⊢app₁ ⊢e ⊢e₁) j~Σ = ⊢app (complete ⊢e (~C (complete ⊢e₁ ~∞) j~Σ))
complete (⊢app₂ ⊢e ⊢e₁) j~Σ = ⊢app (complete ⊢e (~I (complete ⊢e₁ ~Z) j~Σ))
complete (⊢sub ⊢e B≤A j≢Z) j~Σ = sub-gen (complete ⊢e ~Z) {!!} {!!} (complete-≤ B≤A j~Σ)
complete (⊢tabs ⊢e) ~Z = ⊢tabs (complete ⊢e ~Z)
