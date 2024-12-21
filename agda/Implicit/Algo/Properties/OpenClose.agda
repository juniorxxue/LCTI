module Implicit.Algo.Properties.OpenClose where

open import Implicit.Language
open import Implicit.Algo.Base
open import Implicit.Algo.Properties.Lookup

----------------------------------------------------------------------
--+                        Inversion Lemmas                        +--
----------------------------------------------------------------------


^∈-∙∈-false :
    Γ ∋^ k
  → Γ ∋∙ k
  → ⊥
^∈-∙∈-false (S^ ^in) (S^ ∙in) = ^∈-∙∈-false ^in ∙in
^∈-∙∈-false (S∙ ^in) (S∙ ∙in) = ^∈-∙∈-false ^in ∙in
^∈-∙∈-false (S, ^in) (S, ∙in) = ^∈-∙∈-false ^in ∙in
^∈-∙∈-false (S= ^in) (S= ∙in) = ^∈-∙∈-false ^in ∙in

^∈-=∈-false :
    Γ ∋^ k
  → Γ ∋= k
  → ⊥
^∈-=∈-false (S^ in1) (S^ in2) = ^∈-=∈-false in1 in2
^∈-=∈-false (S∙ in1) (S∙ in2) = ^∈-=∈-false in1 in2
^∈-=∈-false (S, in1) (S, in2) = ^∈-=∈-false in1 in2
^∈-=∈-false (S= in1) (S= in2) = ^∈-=∈-false in1 in2

    
⊢c-^∈-false : k ε A
            → Γ ∋^ k
            → Γ ⊢c A
            → ⊥
⊢c-^∈-false ε-var inΓ (⊢c-var-∙ x) = ^∈-∙∈-false inΓ x
⊢c-^∈-false ε-var inΓ (⊢c-var-= x) = ^∈-=∈-false inΓ x
⊢c-^∈-false (ε-arr-l inA) inΓ (⊢c-arr cloA cloA₁) = ⊢c-^∈-false inA inΓ cloA
⊢c-^∈-false (ε-arr-r inA) inΓ (⊢c-arr cloA cloA₁) = ⊢c-^∈-false inA inΓ cloA₁
⊢c-^∈-false (ε-∀ inA) inΓ (⊢c-∀ cloA) = ⊢c-^∈-false inA (S∙ inΓ) cloA

{-
test : Γ ,= B ⊢c A
     → Γ ,∙ ⊢c A
-}     

-- in k position, we replace a ,= B with ,∙
infix 3 _◆_⇘_
data _◆_⇘_ : Env n m → Fin m → Env n m → Set where
  ◆Z : Γ ,= A ◆ #0 ⇘ Γ ,∙
  ◆S, : Γ ◆ k ⇘ Γ'
      → Γ , A ◆ k ⇘ Γ' , A
  ◆S∙ : Γ ◆ k ⇘ Γ'
      → Γ ,∙ ◆ #S k ⇘ Γ' ,∙
  ◆S= : Γ ◆ k ⇘ Γ'
      → Γ ,= A ◆ #S k ⇘ Γ' ,= A
  ◆S^ : Γ ◆ k ⇘ Γ'
      → Γ ,^ ◆ #S k ⇘ Γ' ,^

◆-∙∈ : Γ ∋∙ X
     → Γ ◆ k ⇘ Γ'
     → Γ' ∋∙ X
◆-∙∈ (S= inΓ) ◆Z = S∙ inΓ
◆-∙∈ (S, inΓ) (◆S, ◆Γ) = S, (◆-∙∈ inΓ ◆Γ)
◆-∙∈ Z (◆S∙ ◆Γ) = Z
◆-∙∈ (S∙ inΓ) (◆S∙ ◆Γ) = S∙ (◆-∙∈ inΓ ◆Γ)
◆-∙∈ (S= inΓ) (◆S= ◆Γ) = S= (◆-∙∈ inΓ ◆Γ)
◆-∙∈ (S^ inΓ) (◆S^ ◆Γ) = S^ (◆-∙∈ inΓ ◆Γ)

-- should this A exposed to the outside?
◆-=∈-≢ : Γ ∋= X
     → Γ ◆ k ⇘ Γ'
     → k ≢ X
     → Γ' ∋= X
◆-=∈-≢ Z ◆Z neq = ⊥-elim (neq refl)
◆-=∈-≢ Z (◆S= ◆Γ) neq = Z
◆-=∈-≢ (S, inΓ) (◆S, ◆Γ) neq = S, (◆-=∈-≢ inΓ ◆Γ neq)
◆-=∈-≢ (S^ inΓ) (◆S^ ◆Γ) neq = S^ (◆-=∈-≢ inΓ ◆Γ (≢-pred neq))
◆-=∈-≢ (S∙ inΓ) (◆S∙ ◆Γ) neq = S∙ (◆-=∈-≢ inΓ ◆Γ (≢-pred neq))
◆-=∈-≢ (S= inΓ) ◆Z neq = S∙ inΓ
◆-=∈-≢ (S= inΓ) (◆S= ◆Γ) neq = S= (◆-=∈-≢ inΓ ◆Γ (≢-pred neq))

◆-=∈-≡ : Γ ∋= k
     → Γ ◆ k ⇘ Γ'
     → Γ' ∋∙ k
◆-=∈-≡ Z ◆Z = Z
◆-=∈-≡ (S, inΓ) (◆S, ◆Γ) = S, (◆-=∈-≡ inΓ ◆Γ)
◆-=∈-≡ (S^ inΓ) (◆S^ ◆Γ) = S^ (◆-=∈-≡ inΓ ◆Γ)
◆-=∈-≡ (S∙ inΓ) (◆S∙ ◆Γ) = S∙ (◆-=∈-≡ inΓ ◆Γ)
◆-=∈-≡ (S= inΓ) (◆S= ◆Γ) = S= (◆-=∈-≡ inΓ ◆Γ)

⊢c-◆ : Γ ⊢c A
     → Γ ◆ k ⇘ Γ'
     → Γ' ⊢c A
⊢c-◆ ⊢c-int ◆Γ = ⊢c-int
⊢c-◆ (⊢c-var-∙ inΓ) ◆Γ = ⊢c-var-∙ (◆-∙∈ inΓ ◆Γ)
⊢c-◆ {k = k} (⊢c-var-= {X = X} inΓ) ◆Γ with k #≟ X
... | yes refl = ⊢c-var-∙ (◆-=∈-≡ inΓ ◆Γ)
... | no ¬p = ⊢c-var-= (◆-=∈-≢ inΓ ◆Γ ¬p)
⊢c-◆ (⊢c-arr clo clo₁) ◆Γ = ⊢c-arr (⊢c-◆ clo ◆Γ) (⊢c-◆ clo₁ ◆Γ)
⊢c-◆ (⊢c-∀ clo) ◆Γ = ⊢c-∀ (⊢c-◆ clo (◆S∙ ◆Γ))

⊢c-◆0 : Γ ,= B ⊢c A
      → Γ ,∙ ⊢c A
⊢c-◆0 clo = ⊢c-◆ clo ◆Z

----------------------------------------------------------------------
--+                           Extension                            +--
----------------------------------------------------------------------


⊆-closed : Γ ⊢c A
         → Γ ⊆ Γ'
         → Γ' ⊢c A
⊆-closed ⊢c-int ss = ⊢c-int
⊆-closed (⊢c-var-∙ x) ss = ⊢c-var-∙ (⊆-in∙ x ss)
⊆-closed (⊢c-var-= x) ss = ⊢c-var-= (⊆-in= x ss)
⊆-closed (⊢c-arr clo clo₁) ss = ⊢c-arr (⊆-closed clo ss) (⊆-closed clo₁ ss)
⊆-closed (⊢c-∀ clo) ss = ⊢c-∀ (⊆-closed clo (uvar ss))

⊆-closedᵉ : Γ ⊢cᵉ e
          → Γ ⊆ Γ'
          → Γ' ⊢cᵉ e
⊆-closedᵉ ⊢c-lit ss = ⊢c-lit
⊆-closedᵉ (⊢c-var inΓ clo) ss = {!ss!}
⊆-closedᵉ (⊢c-lam clo) ss = ⊢c-lam (⊆-closedᵉ clo (var ss))
⊆-closedᵉ (⊢c-app clo clo₁) ss = ⊢c-app (⊆-closedᵉ clo ss) (⊆-closedᵉ clo₁ ss)
⊆-closedᵉ (⊢c-ann x clo) ss = ⊢c-ann (⊆-closed x ss) (⊆-closedᵉ clo ss)
⊆-closedᵉ (⊢c-tlam clo) ss = ⊢c-tlam (⊆-closedᵉ clo (uvar ss))

⊆-closedᶜ : Γ ⊢cᶜ Σ
          → Γ ⊆ Γ'
          → Γ' ⊢cᶜ Σ
⊆-closedᶜ ⊢c-empty ss = ⊢c-empty
⊆-closedᶜ (⊢c-τ cloA) ss = ⊢c-τ (⊆-closed cloA ss)
⊆-closedᶜ (⊢c-term cloe clo) ss = ⊢c-term (⊆-closedᵉ cloe ss) (⊆-closedᶜ clo ss)


----------------------------------------------------------------------
--+                            Polarity                            +--
----------------------------------------------------------------------


polar-arr-l : Polarity Γ (A `→ B) (τ (C `→ D)) ≤
            → Polarity Γ C (τ A) (⋆ ≤)
polar-arr-l (polar-l (⊢c-arr cloA cloA₁)) = polar-r (⊢c-τ cloA)
polar-arr-l (polar-r (⊢c-τ (⊢c-arr cloA cloA₁))) = polar-l cloA

polar-arr-r : Polarity Γ (A `→ B) (τ (C `→ D)) ≤
            → Polarity Γ B (τ D) ≤
polar-arr-r (polar-l (⊢c-arr cloA cloA₁)) = polar-l cloA₁
polar-arr-r (polar-r (⊢c-τ (⊢c-arr cloA cloA₁))) = polar-r (⊢c-τ cloA₁)

polar-∀ : Polarity Γ (`∀ A) (τ (`∀ B)) ≤
        → Polarity (Γ ,∙) A (τ B) ≤
polar-∀ (polar-l (⊢c-∀ cloA)) = polar-l cloA
polar-∀ (polar-r (⊢c-τ (⊢c-∀ cloA))) = polar-r (⊢c-τ cloA)

polar-⊆ : Polarity Γ A Σ ≤
        → Γ ⊆ Γ'
        → Polarity Γ' A Σ ≤
polar-⊆ (polar-l cloA) ss = polar-l (⊆-closed cloA ss)
polar-⊆ (polar-r cloA) ss = polar-r (⊆-closedᶜ cloA ss)

----------------------------------------------------------------------
--+                   Inference result is closed                   +--
----------------------------------------------------------------------

result-closed : Γ ⊢ Σ ⇒ e ⇒ A
              → Γ ⊢cᶜ Σ
              → Γ ⊢cᵉ e
              → Γ ⊢c A
result-closed ⊢lit cloΣ cloe = ⊢c-int
result-closed (⊢var x∈Γ) cloΣ (⊢c-var inΓ clo) rewrite ∋⦂-unique x∈Γ inΓ = clo
result-closed (⊢ann ⊢e) cloΣ (⊢c-ann cloA cloe) = cloA
result-closed (⊢app ⊢e) cloΣ (⊢c-app cloe cloe₁) with result-closed ⊢e (⊢c-term cloe₁ cloΣ) cloe
... | ⊢c-arr ind ind₁ = ind₁
result-closed (⊢lam₁ ⊢e) (⊢c-τ (⊢c-arr cloA cloA₁)) (⊢c-lam cloe) =
  ⊢c-arr cloA (⊢c-weaken0 (result-closed ⊢e (⊢c-τ (⊢c-strengthen0 cloA₁)) {!!}))
result-closed (⊢lam₂ ⊢e up-c ⊢e₁) cloΣ cloe = {!!}
result-closed (⊢sub ⊢e ne gc s) cloΣ cloe = {!!}
result-closed (⊢tabs ⊢e) cloΣ cloe = {!!}
