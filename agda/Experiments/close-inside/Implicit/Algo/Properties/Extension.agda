module Implicit.Algo.Properties.Extension where

open import Implicit.Language
open import Implicit.Algo.Base

polar-⊆ : Polarity Γ A Σ ≤
        → Γ ⊆ Γ'
        → Polarity Γ' A Σ ≤
polar-⊆ (polar-l cloΓ cloA) ss = polar-l (⊆-closed cloΓ ss) (⊆-cloA cloA ss)
polar-⊆ (polar-r cloΓ cloA) ss = polar-r (⊆-closed cloΓ ss) {!!}

s-⊆ : Γ ⊢ A ⌞ ≤ ⌝ Σ ⊣ Γ' ↪ B
    → Polarity Γ A Σ ≤
    → Γ ⊆ Γ'
s-⊆ s-int pr = ⊆-refl
s-⊆ (s-empty clo) pr = ⊆-refl
s-⊆ s-var pr = ⊆-refl
s-⊆ (s-ex-l^ x-in inst) (polar-r cloΓ (⊢c-τ cloA)) = inst-⊆ inst cloA
s-⊆ (s-ex-l= x-in s) pr = s-⊆ s (polar-in-l pr x-in)
s-⊆ (s-ex-r^ x-in inst) (polar-l cloΓ cloA) = inst-⊆ inst cloA
s-⊆ (s-ex-r= x-in s) pr = s-⊆ s (polar-in-r pr x-in)
s-⊆ (s-arr s s₁) pr = ⊆-trans (s-⊆ s (polar-arr-l pr)) (s-⊆ s₁ (polar-⊆ (polar-arr-r pr) (s-⊆ s ((polar-arr-l pr)))))
s-⊆ (s-term-c ⊢e s) pr = s-⊆ s (polar-tm-r pr)
s-⊆ (s-term-o opnA ⊢e s s₁) (polar-r cloΓ cloΣ) with s-⊆ s (polar-l cloΓ {!!})
... | r = {!!}
s-⊆ (s-∀ s) pr = {!!}
s-⊆ (s-∀l s upᶜ upᵉ st₁ st₂) pr = {!!}

{-
s-⊆ s-int = ⊆-refl
s-⊆ (s-empty clo) = ⊆-refl
s-⊆ s-var = ⊆-refl
s-⊆ (s-ex-l^ x-in inst) = inst-⊆ inst {!!}
s-⊆ (s-ex-l= x-in s) = s-⊆ s
s-⊆ (s-ex-r^ x-in inst) = inst-⊆ inst {!!}
s-⊆ (s-ex-r= x-in s) = s-⊆ s
s-⊆ (s-arr s s₁) = ⊆-trans (s-⊆ s) (s-⊆ s₁)
s-⊆ (s-term-c ⊢e s) = s-⊆ s
s-⊆ (s-term-o opnA ⊢e s s₁) = ⊆-trans (s-⊆ s) (s-⊆ s₁)
s-⊆ (s-∀ s) with s-⊆ s
... | uvar ind = ind
s-⊆ (s-∀l s upᶜ upᵉ st₁ st₂) with s-⊆ s
... | evar-sol ind clo = {!!}
-}
