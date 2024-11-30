module Implicit.Algo.Properties.OpenClose where

open import Implicit.Language
open import Implicit.Algo.Base

private variable
  Ψ Ψ' : SEnv n m
  A B : Type m
  Σ : Context n m
  k X : Fin m

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


polarity⁺ :
    Ψ ⊢ A ≤⁺ Σ ⊣ Ψ' ↪ B
  → Ψ ⊢cᶜ Σ

polarity⁻ :
    Ψ ⊢ A ≤⁻ Σ ⊣ Ψ' ↪ B
  → Ψ ⊢c A

polarity⁺ s⁺-int = ⊢c-τ ⊢c-int
polarity⁺ (s⁺-empty p) = ⊢c-empty
polarity⁺ (s⁺-var clo) = ⊢c-τ clo
polarity⁺ (s⁺-ex-l^ clo x-in inst) = ⊢c-τ clo
polarity⁺ (s⁺-ex-l= clo x-in s) = polarity⁺ s
polarity⁺ (s⁺-ex-r= clo x-in s) = ⊢c-τ (⊢c-var-= x-in)
polarity⁺ (s⁺-arr cloC cloD x s) = ⊢c-τ (⊢c-arr cloC cloD)
polarity⁺ (s⁺-term-c cloA cloΣ ⊢e s) = ⊢c-term (polarity⁺ s)
polarity⁺ (s⁺-term-o opnA cloΣ ⊢e x s) = ⊢c-term cloΣ
polarity⁺ (s⁺-∀ cloB s) = ⊢c-τ cloB
polarity⁺ (s⁺-∀l cloΣ s upᶜ upᵉ st₁ st₂) = ⊢c-term cloΣ

polarity⁻ s⁻-int = ⊢c-int
polarity⁻ (s⁻-var clo) = clo
polarity⁻ (s⁻-ex-r^ clo x-in inst) = clo
polarity⁻ (s⁻-ex-l= clo x-in s) = ⊢c-var-= x-in
polarity⁻ (s⁻-ex-r= clo x-in s) = clo
polarity⁻ (s⁻-arr cloA cloB x s) = ⊢c-arr cloA cloB
polarity⁻ (s⁻-∀ cloA s) = cloA


----------------------------------------------------------------------
--+                        Inversion Lemmas                        +--
----------------------------------------------------------------------


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

{-
test : Ψ ,= B ⊢c A
     → Ψ ,∙ ⊢c A
-}     

-- in k position, we replace a ,= B with ,∙
infix 3 _◆_⇘_
data _◆_⇘_ : SEnv n m → Fin m → SEnv n m → Set where
  ◆Z : Ψ ,= A ◆ #0 ⇘ Ψ ,∙
  ◆S, : Ψ ◆ k ⇘ Ψ'
      → Ψ , A ◆ k ⇘ Ψ' , A
  ◆S∙ : Ψ ◆ k ⇘ Ψ'
      → Ψ ,∙ ◆ #S k ⇘ Ψ' ,∙
  ◆S= : Ψ ◆ k ⇘ Ψ'
      → Ψ ,= A ◆ #S k ⇘ Ψ' ,= A
  ◆S^ : Ψ ◆ k ⇘ Ψ'
      → Ψ ,^ ◆ #S k ⇘ Ψ' ,^

◆-∙∈ : X ∙∈ Ψ
     → Ψ ◆ k ⇘ Ψ'
     → X ∙∈ Ψ'
◆-∙∈ (S= inΨ) ◆Z = S∙ inΨ
◆-∙∈ (S, inΨ) (◆S, ◆Ψ) = S, (◆-∙∈ inΨ ◆Ψ)
◆-∙∈ Z (◆S∙ ◆Ψ) = Z
◆-∙∈ (S∙ inΨ) (◆S∙ ◆Ψ) = S∙ (◆-∙∈ inΨ ◆Ψ)
◆-∙∈ (S= inΨ) (◆S= ◆Ψ) = S= (◆-∙∈ inΨ ◆Ψ)
◆-∙∈ (S^ inΨ) (◆S^ ◆Ψ) = S^ (◆-∙∈ inΨ ◆Ψ)

◆-=∈-≢ : X := A ∈ Ψ
     → Ψ ◆ k ⇘ Ψ'
     → k ≢ X
     → X := A ∈ Ψ'
◆-=∈-≢ (Z up) ◆Z neq = ⊥-elim (neq refl)
◆-=∈-≢ (Z up) (◆S= ◆Ψ) neq = Z up
◆-=∈-≢ (S, inΨ) (◆S, ◆Ψ) neq = S, (◆-=∈-≢ inΨ ◆Ψ neq)
◆-=∈-≢ (S^ inΨ up) (◆S^ ◆Ψ) neq = S^ (◆-=∈-≢ inΨ ◆Ψ (≢-pred neq)) up
◆-=∈-≢ (S∙ inΨ up) (◆S∙ ◆Ψ) neq = S∙ (◆-=∈-≢ inΨ ◆Ψ (≢-pred neq)) up
◆-=∈-≢ (S= inΨ st) ◆Z neq = ?
◆-=∈-≢ (S= inΨ st) (◆S= ◆Ψ) neq = S= (◆-=∈-≢ inΨ ◆Ψ (≢-pred neq)) st

⊢c-◆ : Ψ ⊢c A
     → Ψ ◆ k ⇘ Ψ'
     → Ψ' ⊢c A
⊢c-◆ ⊢c-int ◆Ψ = ⊢c-int
⊢c-◆ (⊢c-var-∙ inΨ) ◆Ψ = ⊢c-var-∙ (◆-∙∈ inΨ ◆Ψ)
⊢c-◆ (⊢c-var-= inΨ) ◆Ψ = {!!}
⊢c-◆ (⊢c-arr clo clo₁) ◆Ψ = ⊢c-arr (⊢c-◆ clo ◆Ψ) (⊢c-◆ clo₁ ◆Ψ)
⊢c-◆ (⊢c-∀ clo) ◆Ψ = ⊢c-∀ (⊢c-◆ clo (◆S∙ ◆Ψ))
