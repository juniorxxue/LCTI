module Implicit.Algo.Properties.EnvironmentsMain2 where
-- version : Closed in lemma

open import Implicit.Language
open import Implicit.Algo.Base
open import Implicit.Algo.Properties.Extension
open import Implicit.Algo.Properties.OpenClose
open import Implicit.Algo.Properties.Polarity
open import Implicit.Algo.Properties.Environments

postulate
  s-⊆-prv : Γ ⊢ A ≤ Σ ⊣ Γ ↪ B
          → Γ ⊆ Δ
          → Δ ⊢ A ≤ Σ ⊣ Δ ↪ B


t-⊆-prv : Γ ⊢ Σ ⇒ e ⇒ A
        → Γ ⊆ Δ
        → Δ ⊢ Σ ⇒ e ⇒ A

{-
T ++ T2 |- A <: S -| T ++ T3 ~~> B ->
fv(A) in T2   <-- unsolved variables in A must be in T2
------------------------------------
D ++ T2 |- A <: S -| D ++ T3 ~~> B
-}

s-⊆-prv-gen : Γ₁ ⊢ A ≤ Σ ⊣ Γ₂ ↪ B
            → Γ₁ ∤ k ⊢o A
            → Γ₁ ⊆ Δ₁ ∣ Γ₂ ⊆ Δ₂ by k -- consistently replace the inner envs, keep the outer envs, distinguished by k-th position
            → Δ₁ ⊢ A ≤ Σ ⊣ Δ₂ ↪ B

s-⊆-prv-gen s = {!!}

t-⊆-prv = {!!}

clo-opnx : Γ ⊢c A
         → Γ ∤ k ⊢o A
clo-opnx ⊢c-int = opn-int
clo-opnx (⊢c-var-∙ inΓ) = opn-var (opnx∙ inΓ)
clo-opnx (⊢c-var-= inΓ) = opn-var (opnx= inΓ)
clo-opnx (⊢c-arr clo clo₁) = opn-arr (clo-opnx clo) (clo-opnx clo₁)
clo-opnx (⊢c-∀ clo) = opn-∀ (clo-opnx clo)

s-⊆-prv' : Γ ⊢ A ≤ Σ ⊣ Γ ↪ B
         → Γ ⊢c A
         → Γ ⊢cᶜ Σ
         → Γ ⊆ Δ
         → Δ ⊢ A ≤ Σ ⊣ Δ ↪ B
