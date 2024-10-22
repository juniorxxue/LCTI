module Implicit.Algo.Subst.Lemmas where

open import Implicit.Common
open import Implicit.Algo
open import Implicit.Algo.Subst.Definitions

postulate
  env-remove-unique : ∀ {Ψ : SEnv n (1 + m)} {Ψ₁ Ψ₂ k T}
    → Ψ / k ⦂ T ⇨ Ψ₁
    → Ψ / k ⦂ T ⇨ Ψ₂
    → Ψ₁ ≡ Ψ₂

substituition : ∀ {Ψ Ψ' k T A B A' Ψx Ψx' Σ' B'}
  → Ψ ⊢ A ≤ Σ ⊣ Ψ' ↪ B
  → Ψ / k ⦂ T ⇨ Ψx
  → Ψ' / k ⦂ T ⇨ Ψx'
  → [ k / T ]ˢ A ⇨ A'
  → [ k / T ]ᶜ Σ ⇨ Σ'
  → [ k / T ]ˢ B ⇨ B'
  → Ψx ⊢ A' ≤ Σ' ⊣ Ψx' ↪ B'
substituition s-int env1 env2 st-int (fulltype st-int) st-int rewrite env-remove-unique env1 env2 = s-int
substituition (s-empty p) env1 env2 st1 empty st2 rewrite env-remove-unique env1 env2 rewrite subst-unique' st1 st2 = s-empty {!!}
substituition s-var env1 env2 st1 stΣ st2 = {!!}
substituition (s-ex-l^ clo x-in inst) env1 env2 st1 stΣ st2 = {!!}
substituition (s-ex-l= clo x-in s) env1 env2 st1 stΣ st2 = {!!}
substituition (s-ex-r^ clo x-in inst) env1 env2 st1 stΣ st2 = {!!}
substituition (s-ex-r= clo x-in s) env1 env2 st1 stΣ st2 = {!!}
substituition (s-arr s s₁) env1 env2 st1 stΣ st2 = {!!}
substituition (s-term-c cloA cloB ⊢e s) env1 env2 st1 stΣ st2 = {!!}
substituition (s-term-o op ⊢e s s₁) env1 env2 st1 stΣ st2 = {!!}
substituition (s-∀ s) env1 env2 st1 stΣ st2 = {!!}
substituition (s-∀l-^ s) env1 env2 st1 stΣ st2 = {!!}
substituition (s-∀l-eq s st₁ st₂) env1 env2 st1 stΣ st2 = {!!}
  

