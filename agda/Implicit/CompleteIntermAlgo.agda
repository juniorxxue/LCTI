module Implicit.CompleteIntermAlgo where

open import Implicit.Language.All hiding (_≤_; _⊆_w/v_; _⊆_w/t_)
open import Implicit.Algo.All
open import Implicit.Interm.All

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

infix 3 _⊆_w/v_
data _⊆_w/v_ : Env n m → Env n m → Fin m → Set where
  ext-Z^ : (cloA : Γ ⊢c A)
         → Γ ,^ ⊆ Γ ,= A w/v #0
  ext-Z∙ : Γ ,∙ ⊆ Γ ,∙ w/v #0
  ext-S, : Γ ⊆ Δ w/v k
         → Γ , A ⊆ Δ , A w/v k
  ext-S^ : Γ ⊆ Δ w/v k
         → Γ ,^ ⊆ Δ ,^ w/v #S k
  ext-S∙ : Γ ⊆ Δ w/v k
         → Γ ,∙ ⊆ Δ ,∙ w/v #S k
  ext-S= : Γ ⊆ Δ w/v k
         → Γ ,= A ⊆ Δ ,= A w/v #S k

infix 3 _⊆_w/t_
data _⊆_w/t_ : Env n m → Env n m → Type m → Set where
  ext-int : Γ ⊆ Γ w/t Int
  ext-var : Γ ⊆ Δ w/v X
          → Γ ⊆ Δ w/t ‶ X
  ext-arr : Γ ⊆ Ω w/t A
          → Ω ⊆ Δ w/t B
          → Γ ⊆ Δ w/t A `→ B
  ext-∀   : Γ ,∙ ⊆ Δ ,∙ w/t A
          → Γ ⊆ Δ w/t `∀ A

complete-≤ : Δ ⊢ j # A ≤ B
           → Γ ⊆ Δ w/t A
           → Γ ⊢ ⟨ j , B ⟩ ~ Σ
           → Γ ⊢ A ⌞ ≤ ⌝ Σ ⊣ Δ ↪ B
complete-≤ (s-refl cloΓ cloA) ext ~Z = {!!}
complete-≤ (s-int cloΓ) ext j~Σ = {!!}
complete-≤ (s-var-∙ cloΓ inΓ) ext j~Σ = {!!}
complete-≤ (s-var-= cloΓ inΓ) ext j~Σ = {!!}
complete-≤ (s-arr₁ s s₁) (ext-arr ext ext₁) ~∞ = s-arr (complete-≤ s {!!} ~∞) (complete-≤ s₁ {!!} ~∞)
complete-≤ (s-arr₂ s s₁) (ext-arr ext ext₁) (~I ⊢e j~Σ) = {!!}
complete-≤ (s-arr₃ cloA s) ext j~Σ = {!taiji!}
complete-≤ (s-∀ s) ext j~Σ = {!!}
complete-≤ (s-∀l s ic fd stC stD) ext j~Σ = {!!}
complete-≤ (s-var-l inΓ s) ext j~Σ = {!!}
complete-≤ (s-var-r inΓ s) ext j~Σ = {!!}
