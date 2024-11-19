module Implicit.Algo.Properties.OpenClose where

open import Implicit.Language
open import Implicit.Algo.Base

private variable
  Ψ Ψ' : SEnv n m
  A B : Type m
  Σ : Context n m
  k : Fin m

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

  s-closed-r : ∀ {Ψ : SEnv n m} {Γ A B Σ}
    → 𝕎 Γ ⊢ A ≤ Σ ⊣ Ψ ↪ B
    → 𝕎 Γ ⊢ A ≤ Σ ⊣ 𝕎 Γ ↪ B

  s-closed-l : ∀ {Ψ : SEnv n m} {Γ A B Σ}
    → Ψ ⊢ A ≤ Σ ⊣ 𝕎 Γ ↪ B
    → 𝕎 Γ ⊢ A ≤ Σ ⊣ 𝕎 Γ ↪ B

  ⊢c-⊢o-⊥ : Ψ ⊢c A → Ψ ⊢o A → ⊥

  ⊢c-, : Ψ ⊢c A → Ψ , B ⊢c A


{-
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

ex-one-side :
    Ψ ⊢ A ≤ Σ ⊣ Ψ' ↪ B
  → OneSide Ψ A Σ
ex-one-side s-int = none ⊢c-int (⊢c-τ ⊢c-int)
ex-one-side (s-empty p) = none p ⊢c-empty
ex-one-side (s-var clo) = none clo (⊢c-τ clo)
ex-one-side (s-ex-l^ clo x-in inst) = left {!!} (⊢c-τ clo)
ex-one-side (s-ex-l= clo x-in s) = {!!}
ex-one-side (s-ex-r^ clo x-in inst) = {!!}
ex-one-side (s-ex-r= clo x-in s) = {!!}

ex-one-side (s-arr s s₁) = {!!}
ex-one-side (s-term-c cloA ⊢e s) = {!!}
ex-one-side (s-term-o opnA ⊢e s s₁) = {!!}
ex-one-side (s-∀ s) = {!!}
ex-one-side (s-∀l s upᶜ upᵉ st₁ st₂) = {!!}
-}



⊢c-^∈-false' :
  k ^∈ Ψ → Ψ ⊢c ‶ k → ⊥
⊢c-^∈-false' (S^ ^in) (⊢c-var^S clo) = ⊢c-^∈-false' ^in clo
⊢c-^∈-false' (S∙ ^in) (⊢c-var∙S clo) = ⊢c-^∈-false' ^in clo
⊢c-^∈-false' (S, ^in) (⊢c-var,S clo) = ⊢c-^∈-false' ^in clo
⊢c-^∈-false' (S= ^in) (⊢c-var=S clo) = ⊢c-^∈-false' ^in clo
    
⊢c-^∈-false : k ε A
            → k ^∈ Ψ
            → Ψ ⊢c A
            → ⊥
⊢c-^∈-false ε-var inΨ cloA = ⊢c-^∈-false' inΨ cloA
⊢c-^∈-false (ε-arr-l inA) inΨ (⊢c-arr cloA cloA₁) = ⊢c-^∈-false inA inΨ cloA
⊢c-^∈-false (ε-arr-r inA) inΨ (⊢c-arr cloA cloA₁) = ⊢c-^∈-false inA inΨ cloA₁
⊢c-^∈-false (ε-∀ inA) inΨ (⊢c-∀ cloA) = ⊢c-^∈-false inA (S∙ inΨ) cloA

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
