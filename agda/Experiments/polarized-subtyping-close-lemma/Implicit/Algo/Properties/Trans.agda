module Implicit.Algo.Trans where

-- not exactly like transitivity in classic subtyping
-- since we don't subsume it
-- it only describes the relation between *updates contexts*, used in subsumption lemma in ⊢sub case

open import Implicit.Common
open import Implicit.Algo
open import Implicit.Algo.Postulates

postulate

  s-trans : ∀ {Ψ : SEnv n m} {A Σ Σ' Σ'' Ψ' Ψ'' A' a̅ A''}
    → Ψ ⊢ A ≤ Σ ⊣ Ψ' ↪ A'
    → ⟦ Σ ⟧⇒⟦ a̅ , □ ⟧  
    → a̅ ⊕ Σ'' := Σ'
    → Ψ ⊢ A' ≤ Σ' ⊣ Ψ'' ↪ A''
    → Ψ ⊢ A ≤ Σ' ⊣ Ψ'' ↪ A''

{-
s-trans' : ∀ {Ψ : SEnv n m} {A Σ Σ' Σ'' Ψ' Ψ'' A' a̅ A''}
  → Ψ ⊢ A ≤ Σ ⊣ Ψ' ↪ A'
  → ⟦ Σ ⟧⇒⟦ a̅ , □ ⟧  
  → a̅ ⊕ Σ'' := Σ'
  → Ψ ⊢ A' ≤ Σ' ⊣ Ψ'' ↪ A''
  → Ψ ⊢ A ≤ Σ' ⊣ Ψ'' ↪ A''
s-trans' (s-empty p) none-□ ch s2 = s2
s-trans' (s-term-c cloA cloB ⊢e s1) (have-e spl) (⊕cons-e ch) (s-term-c cloA₁ cloB₁ ⊢e₁ s2) = s-term-c cloA cloB {!!} (s-trans' s1 spl ch s2) -- easy
s-trans' (s-term-c cloA cloB ⊢e s1) (have-e spl) (⊕cons-e ch) (s-term-o op ⊢e₁ s2 s3) = {!!}
s-trans' (s-term-o op ⊢e s1 s3) (have-e spl) (⊕cons-e ch) (s-term-c cloA cloB ⊢e₁ s2) = {!!}
s-trans' (s-term-o op ⊢e s1 s3) (have-e spl) (⊕cons-e ch) (s-term-o op₁ ⊢e₁ s2 s4) = {!!}
s-trans' (s-∀l-^ s1) (have-e spl) (⊕cons-e ch) s2 = s-∀l-^ (s-trans' s1 {!!} {!!} {!!})
s-trans' (s-∀l-eq s1 st₁ st₂) spl ch s2 = {!!}
-}
