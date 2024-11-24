module Implicit.Algo.Properties.OpenClose where

open import Implicit.Language
open import Implicit.Algo.Base

private variable
  Ψ Ψ' : SEnv n m
  A B : Type m
  Σ : Context n m
  k : Fin m
  ≤ : Polar

postulate
  ⊢a→⊢c : ∀ {Γ : Env n m} {Σ e A}
    → Γ ⊢ Σ ⇒ e ⇒ A
    → 𝕎 Γ ⊢c A

  ⊢a→⊢c-τ : ∀ {Γ : Env n m} {e A B}
    → Γ ⊢ τ B ⇒ e ⇒ A
    → 𝕎 Γ ⊢c B

  ⊢a→⊢c-weaken : ∀ {Γ : Env n m} {Σ e A B}
    → Γ , B ⊢ Σ ⇒ e ⇒ A
    → 𝕎 Γ ⊢c A

{-
  s-closed-r : ∀ {Ψ : SEnv n m} {Γ A B Σ}
    → 𝕎 Γ ⊢ A ≤ Σ ⊣ Ψ ↪ B
    → 𝕎 Γ ⊢ A ≤ Σ ⊣ 𝕎 Γ ↪ B

  s-closed-l : ∀ {Ψ : SEnv n m} {Γ A B Σ}
    → Ψ ⊢ A ≤ Σ ⊣ 𝕎 Γ ↪ B
    → 𝕎 Γ ⊢ A ≤ Σ ⊣ 𝕎 Γ ↪ B
-}    

  ⊢c-⊢o-⊥ : Ψ ⊢c A → Ψ ⊢o A → ⊥

  ⊢c-, : Ψ ⊢c A → Ψ , B ⊢c A


data OneSide (Ψ : SEnv n m) (A : Type m) (Σ : Context n m) : Set where
  left  : (opn : Ψ ⊢o A)
        → (clo : Ψ ⊢cᶜ Σ)
        → OneSide Ψ A Σ
  right : (clo : Ψ ⊢c A)
        → (opn : Ψ ⊢oᶜ Σ)
        → OneSide Ψ A Σ
  none  : (clo₁ : Ψ ⊢c A)
        → (clo₂ : Ψ ⊢cᶜ Σ)
        → OneSide Ψ A Σ

polarity⁺ :
    Ψ ⊢ A ⌞ ≤⁺ ⌝ Σ ⊣ Ψ' ↪ B
  → Ψ ⊢cᶜ Σ

polarity⁻ :
    Ψ ⊢ A ⌞ ≤⁻ ⌝ Σ ⊣ Ψ' ↪ B
  → Ψ ⊢c A

polarity⁺ s-int = ⊢c-τ ⊢c-int
polarity⁺ (s-empty p) = ⊢c-empty
polarity⁺ (s-var clo) = ⊢c-τ clo
polarity⁺ (s-ex-l^ clo x-in inst) = ⊢c-τ clo
polarity⁺ (s-ex-l= clo x-in s) = polarity⁺ s
polarity⁺ (s-ex-r= clo x-in s) = ⊢c-τ (⊢c-var-= x-in)
polarity⁺ (s-arr s s₁) with polarity⁻ s | polarity⁺ s₁
... | ind1 | ⊢c-τ x = ⊢c-τ (⊢c-arr ind1 {!!})
polarity⁺ (s-term-c cloA ⊢e s) = {!!}
polarity⁺ (s-term-o opnA ⊢e s s₁) = {!!}
polarity⁺ (s-∀ s) = {!!}
polarity⁺ (s-∀l s upᶜ upᵉ st₁ st₂) = {!!}

polarity⁻ s-int = {!!}
polarity⁻ (s-empty p) = {!!}
polarity⁻ (s-var clo) = {!!}
polarity⁻ (s-ex-l= clo x-in s) = {!!}
polarity⁻ (s-ex-r^ clo x-in inst) = {!!}
polarity⁻ (s-ex-r= clo x-in s) = {!!}
polarity⁻ (s-arr s s₁) = {!!}
polarity⁻ (s-∀ s) = {!!}


ex-one-side :
    Ψ ⊢ A ⌞ ≤ ⌝ Σ ⊣ Ψ' ↪ B
  → OneSide Ψ A Σ


^∈-∙∈-false :
    k ^∈ Ψ
  → k ∙∈ Ψ
  → ⊥
^∈-∙∈-false (S^ ^in) (S^ ∙in) = ^∈-∙∈-false ^in ∙in
^∈-∙∈-false (S∙ ^in) (S∙ ∙in) = ^∈-∙∈-false ^in ∙in
^∈-∙∈-false (S, ^in) (S, ∙in) = ^∈-∙∈-false ^in ∙in
^∈-∙∈-false (S= ^in) (S= ∙in) = ^∈-∙∈-false ^in ∙in

^∈-=∈-false :
    k ^∈ Ψ
  → k := A ∈ Ψ
  → ⊥
^∈-=∈-false (S^ in1) (S^ in2 up₁) = ^∈-=∈-false in1 in2
^∈-=∈-false (S∙ in1) (S∙ in2 up₁) = ^∈-=∈-false in1 in2
^∈-=∈-false (S, in1) (S, in2) = ^∈-=∈-false in1 in2
^∈-=∈-false (S= in1) (S= in2 st) = ^∈-=∈-false in1 in2

    
⊢c-^∈-false : k ε A
            → k ^∈ Ψ
            → Ψ ⊢c A
            → ⊥
⊢c-^∈-false ε-var inΨ (⊢c-var-∙ x) = ^∈-∙∈-false inΨ x
⊢c-^∈-false ε-var inΨ (⊢c-var-= x) = ^∈-=∈-false inΨ x
⊢c-^∈-false (ε-arr-l inA) inΨ (⊢c-arr cloA cloA₁) = ⊢c-^∈-false inA inΨ cloA
⊢c-^∈-false (ε-arr-r inA) inΨ (⊢c-arr cloA cloA₁) = ⊢c-^∈-false inA inΨ cloA₁
⊢c-^∈-false (ε-∀ inA) inΨ (⊢c-∀ cloA) = ⊢c-^∈-false inA (S∙ inΨ) cloA
