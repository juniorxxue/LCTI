module Implicit.Algo.Subst.Lemmas where

open import Implicit.Common
open import Implicit.Algo
open import Implicit.Algo.Subst.Definitions

postulate
  env-remove-unique : ∀ {Ψ : SEnv n (1 + m)} {Ψ₁ Ψ₂ k T}
    → Ψ / k ⦂ T ⇨ Ψ₁
    → Ψ / k ⦂ T ⇨ Ψ₂
    → Ψ₁ ≡ Ψ₂

c-substitution : ∀ {Ψ : SEnv n (1 + m)} { Ψx k T A A'}
  → Ψ ⊢c A
  → Ψ / k ⦂ T ⇨ Ψx 
  → [ k / T ]ˢ A ⇨ A'
  → Ψx ⊢c A'
c-substitution ⊢c-int env st-int = ⊢c-int
c-substitution ⊢c-var∙0 env (st-var-neq ¬p) = {!   !}
c-substitution ⊢c-var=0 env st-var-eq = {!   !}
c-substitution ⊢c-var=0 env (st-var-neq ¬p) = {!   !}
c-substitution (⊢c-var,S ⊢c) (S, env x) st = {!   !}
c-substitution (⊢c-var∙S ⊢c) env st = {!   !}
c-substitution (⊢c-var^S ⊢c) env st = {!   !}
c-substitution (⊢c-var=S ⊢c) Z (st-var-neq ¬p) = ⊢c
c-substitution (⊢c-var=S ⊢c) (S,= env x x₁) st = {!   !}
c-substitution (⊢c-arr ⊢cA ⊢cB) env (st-arr st st₁) = ⊢c-arr (c-substitution ⊢cA env st) (c-substitution ⊢cB env st₁)
c-substitution (⊢c-∀ ⊢cA) env (st-∀ up₁ st) = ⊢c-∀ (c-substitution ⊢cA (S,∙ env {!   !}) st)

mutual
  ≤-substituition : ∀ {Ψ Ψ' k T A B A' Ψx Ψx' Σ' B'}
    → Ψ ⊢ A ≤ Σ ⊣ Ψ' ↪ B
    → Ψ / k ⦂ T ⇨ Ψx
    → Ψ' / k ⦂ T ⇨ Ψx'
    → [ k / T ]ˢ A ⇨ A'
    → [ k / T ]ᶜ Σ ⇨ Σ'
    → [ k / T ]ˢ B ⇨ B'
    → Ψx ⊢ A' ≤ Σ' ⊣ Ψx' ↪ B'
  ≤-substituition s-int env1 env2 st-int (fulltype st-int) st-int rewrite env-remove-unique env1 env2 = s-int
  ≤-substituition (s-empty p) env1 env2 st1 empty st2 
    with env-remove-unique env1 env2 
  ...  | refl 
      with subst-unique' st1 st2  
  ...     | refl = s-empty (c-substitution p env1 st1)
  ≤-substituition s-var env1 env2 st1 (fulltype x) st2 
    with env-remove-unique env1 env2 
  ...  | refl 
       with subst-unique' st1 st2 
  ≤-substituition s-var env1 env2 st-var-eq (fulltype x) st2 | refl | refl = {!   !}
  ≤-substituition s-var env1 env2 (st-var-neq ¬p) (fulltype x) st2 | refl | refl = {!   !}
  ≤-substituition (s-ex-l^ clo x-in inst) env1 env2 st1 stΣ st2 = {! !}
  ≤-substituition (s-ex-l= clo x-in s) env1 env2 st1 stΣ st2 = {!!}
  ≤-substituition (s-ex-r^ clo x-in inst) env1 env2 st1 stΣ st2 = {!!}
  ≤-substituition (s-ex-r= clo x-in s) env1 env2 st1 stΣ st2 = {!!}
  ≤-substituition (s-arr s s₁) env1 env2 (st-arr st1 st3) (fulltype (st-arr x x₁)) (st-arr st2 st4) 
    with subst-unique' x₁ st4 
  ...  | refl 
      with subst-unique' x st2 
  -- exists a result?
  ...    | refl = s-arr (≤-substituition s env1 {!   !} st2 (fulltype st1) {!   !}) (≤-substituition s₁ {!   !} env2 st3 (fulltype st4) {!   !})
  ≤-substituition (s-term-c cloA cloB ⊢e s) env1 env2 (st-arr st1 st3) (term stΣ ste) (st-arr st2 st4) = s-term-c (c-substitution cloA env1 st1) (c-substitution cloB env1 st3) (⇒-substitution ⊢e env1 (fulltype st1) st2 ste) (≤-substituition s env1 env2 st3 stΣ st4)
  ≤-substituition (s-term-o op ⊢e s s₁) env1 env2 st1 stΣ st2 = {! !}
  -- ↑-unique
  ≤-substituition (s-∀ s) env1 env2 (st-∀ up₂ st1) (fulltype (st-∀ up₁ x)) (st-∀ up₃ st2) = s-∀ (≤-substituition s {!   !} {!   !} {!   !} (fulltype x) {!   !})
  ≤-substituition (s-∀l s st₁ st₂) env1 env2 st1 stΣ st2 = {!  !}

  ⇒-substitution : ∀ {Ψ k T e A A' Ψx Σ' e'}
    → 𝕄 Ψ ⊢ Σ ⇒ e ⇒ A
    → Ψ / k ⦂ T ⇨ Ψx
    → [ k / T ]ᶜ Σ ⇨ Σ'
    → [ k / T ]ˢ A ⇨ A'
    → [ k / T ]ᵗ e ⇨ e'
    → 𝕄 Ψx ⊢ Σ' ⇒ e' ⇒ A'
  ⇒-substitution = {!   !}

  
   
   