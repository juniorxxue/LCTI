module Implicit.Algo.Properties.OpenClose where

open import Implicit.Language
open import Implicit.Algo.Base
open import Implicit.Algo.Properties.Lookup

private variable
  Ψ Ψ' : SEnv n m
  A B C D : Type m
  Σ : Context n m
  k X : Fin m
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

  ⊢c-⊢o-⊥ : Ψ ⊢c A → Ψ ⊢o A → ⊥

  ⊢c-, : Ψ ⊢c A → Ψ , B ⊢c A


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
  → k =∈ Ψ
  → ⊥
^∈-=∈-false (S^ in1) (S^ in2) = ^∈-=∈-false in1 in2
^∈-=∈-false (S∙ in1) (S∙ in2) = ^∈-=∈-false in1 in2
^∈-=∈-false (S, in1) (S, in2) = ^∈-=∈-false in1 in2
^∈-=∈-false (S= in1) (S= in2) = ^∈-=∈-false in1 in2

    
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

-- should this A exposed to the outside?
◆-=∈-≢ : X =∈ Ψ
     → Ψ ◆ k ⇘ Ψ'
     → k ≢ X
     → X =∈ Ψ'
◆-=∈-≢ Z ◆Z neq = ⊥-elim (neq refl)
◆-=∈-≢ Z (◆S= ◆Ψ) neq = Z
◆-=∈-≢ (S, inΨ) (◆S, ◆Ψ) neq = S, (◆-=∈-≢ inΨ ◆Ψ neq)
◆-=∈-≢ (S^ inΨ) (◆S^ ◆Ψ) neq = S^ (◆-=∈-≢ inΨ ◆Ψ (≢-pred neq))
◆-=∈-≢ (S∙ inΨ) (◆S∙ ◆Ψ) neq = S∙ (◆-=∈-≢ inΨ ◆Ψ (≢-pred neq))
◆-=∈-≢ (S= inΨ) ◆Z neq = S∙ inΨ
◆-=∈-≢ (S= inΨ) (◆S= ◆Ψ) neq = S= (◆-=∈-≢ inΨ ◆Ψ (≢-pred neq))

◆-=∈-≡ : k =∈ Ψ
     → Ψ ◆ k ⇘ Ψ'
     → k ∙∈ Ψ'
◆-=∈-≡ Z ◆Z = Z
◆-=∈-≡ (S, inΨ) (◆S, ◆Ψ) = S, (◆-=∈-≡ inΨ ◆Ψ)
◆-=∈-≡ (S^ inΨ) (◆S^ ◆Ψ) = S^ (◆-=∈-≡ inΨ ◆Ψ)
◆-=∈-≡ (S∙ inΨ) (◆S∙ ◆Ψ) = S∙ (◆-=∈-≡ inΨ ◆Ψ)
◆-=∈-≡ (S= inΨ) (◆S= ◆Ψ) = S= (◆-=∈-≡ inΨ ◆Ψ)

⊢c-◆ : Ψ ⊢c A
     → Ψ ◆ k ⇘ Ψ'
     → Ψ' ⊢c A
⊢c-◆ ⊢c-int ◆Ψ = ⊢c-int
⊢c-◆ (⊢c-var-∙ inΨ) ◆Ψ = ⊢c-var-∙ (◆-∙∈ inΨ ◆Ψ)
⊢c-◆ {k = k} (⊢c-var-= {X = X} inΨ) ◆Ψ with k #≟ X
... | yes refl = ⊢c-var-∙ (◆-=∈-≡ inΨ ◆Ψ)
... | no ¬p = ⊢c-var-= (◆-=∈-≢ inΨ ◆Ψ ¬p)
⊢c-◆ (⊢c-arr clo clo₁) ◆Ψ = ⊢c-arr (⊢c-◆ clo ◆Ψ) (⊢c-◆ clo₁ ◆Ψ)
⊢c-◆ (⊢c-∀ clo) ◆Ψ = ⊢c-∀ (⊢c-◆ clo (◆S∙ ◆Ψ))

⊢c-◆0 : Ψ ,= B ⊢c A
      → Ψ ,∙ ⊢c A
⊢c-◆0 clo = ⊢c-◆ clo ◆Z

----------------------------------------------------------------------
--+                           Extension                            +--
----------------------------------------------------------------------


⊆-closed : Ψ ⊢c A
         → Ψ ⊆ Ψ'
         → Ψ' ⊢c A
⊆-closed ⊢c-int ss = ⊢c-int
⊆-closed (⊢c-var-∙ x) ss = ⊢c-var-∙ (⊆-in∙ x ss)
⊆-closed (⊢c-var-= x) ss = ⊢c-var-= (⊆-in= x ss)
⊆-closed (⊢c-arr clo clo₁) ss = ⊢c-arr (⊆-closed clo ss) (⊆-closed clo₁ ss)
⊆-closed (⊢c-∀ clo) ss = ⊢c-∀ (⊆-closed clo (uvar ss))

⊆-closedᶜ : Ψ ⊢cᶜ Σ
          → Ψ ⊆ Ψ'
          → Ψ' ⊢cᶜ Σ
⊆-closedᶜ ⊢c-empty ss = ⊢c-empty
⊆-closedᶜ (⊢c-τ cloA) ss = ⊢c-τ (⊆-closed cloA ss)
⊆-closedᶜ (⊢c-term clo) ss = ⊢c-term (⊆-closedᶜ clo ss)


----------------------------------------------------------------------
--+                            Polarity                            +--
----------------------------------------------------------------------


polar-arr-l : Polarity Ψ (A `→ B) (τ (C `→ D)) ≤
            → Polarity Ψ C (τ A) (⋆ ≤)
polar-arr-l (polar-l (⊢c-arr cloA cloA₁)) = polar-r (⊢c-τ cloA)
polar-arr-l (polar-r (⊢c-τ (⊢c-arr cloA cloA₁))) = polar-l cloA

polar-arr-r : Polarity Ψ (A `→ B) (τ (C `→ D)) ≤
            → Polarity Ψ B (τ D) ≤
polar-arr-r (polar-l (⊢c-arr cloA cloA₁)) = polar-l cloA₁
polar-arr-r (polar-r (⊢c-τ (⊢c-arr cloA cloA₁))) = polar-r (⊢c-τ cloA₁)

polar-∀ : Polarity Ψ (`∀ A) (τ (`∀ B)) ≤
        → Polarity (Ψ ,∙) A (τ B) ≤
polar-∀ (polar-l (⊢c-∀ cloA)) = polar-l cloA
polar-∀ (polar-r (⊢c-τ (⊢c-∀ cloA))) = polar-r (⊢c-τ cloA)

polar-⊆ : Polarity Ψ A Σ ≤
        → Ψ ⊆ Ψ'
        → Polarity Ψ' A Σ ≤
polar-⊆ (polar-l cloA) ss = polar-l (⊆-closed cloA ss)
polar-⊆ (polar-r cloA) ss = polar-r (⊆-closedᶜ cloA ss)
