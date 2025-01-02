module Implicit.Algo.Properties.Environments where

open import Implicit.Language
open import Implicit.Algo.Base
open import Implicit.Algo.Properties.Extension
open import Implicit.Algo.Properties.OpenClose


t-⊆-prv : Γ ⊢ Σ ⇒ e ⇒ A
        → Γ ⊆ Δ
        → Closed Δ
        → Δ ⊢ Σ ⇒ e ⇒ A

postulate
  s-⊆-prv : Γ' ⊢ A ⌞ ≤ ⌝ Σ ⊣ Γ ↪ B
          → Γ ⊢c A
          → Γ ⊢cᶜ Σ
          → Γ ⊆ Δ
          → Δ' ⊢ A ⌞ ≤ ⌝ Σ ⊣ Δ ↪ B

{-
s-⊆-prv' : Γ' ⊢ A ⌞ ≤ ⌝ Σ ⊣ Γ ↪ B
          → Γ ⊢c A
          → Γ ⊢cᶜ Σ
          → Γ ⊆ Δ
          → Δ ⊢ A ⌞ ≤ ⌝ Σ ⊣ Δ ↪ B
s-⊆-prv' s-int clo cloΣ ss = s-int
s-⊆-prv' (s-empty clo₁) clo cloΣ ss = {!!}
s-⊆-prv' s-var clo cloΣ ss = {!!}
s-⊆-prv' (s-ex-l^ x-in inst) clo cloΣ ss = {!!}
s-⊆-prv' (s-ex-l= x-in s) clo cloΣ ss = {!!}
s-⊆-prv' (s-ex-r^ x-in inst) clo cloΣ ss = {!!}
s-⊆-prv' (s-ex-r= x-in s) clo cloΣ ss = {!!}
s-⊆-prv' (s-arr s s₁) clo cloΣ ss = {!!}
s-⊆-prv' (s-term-c ⊢e s) clo cloΣ ss = {!!}
s-⊆-prv' (s-term-o opnA ⊢e s s₁) clo cloΣ ss = {!!}
s-⊆-prv' (s-∀ s) clo cloΣ ss = {!!}
s-⊆-prv' (s-∀l s upᶜ upᵉ st₁ st₂) clo cloΣ ss = s-∀l {!!} {!!} {!!} {!!} {!!}
-}

t-⊆-prv (⊢lit cloΓ) ext cloΔ = ⊢lit cloΔ
t-⊆-prv (⊢var cloΓ x∈Γ) ext cloΔ = ⊢var cloΔ (⊆-in⦂ x∈Γ ext)
t-⊆-prv (⊢ann ⊢e) ext cloΔ = ⊢ann (t-⊆-prv ⊢e ext cloΔ)
t-⊆-prv (⊢app ⊢e) ext cloΔ = ⊢app (t-⊆-prv ⊢e ext cloΔ)
t-⊆-prv ⊢e'@(⊢lam₁ ⊢e) ext cloΔ with ⊢close-τ ⊢e'
... | (⊢c-arr cloA cloB) with t-⊆-prv ⊢e (var ext) (clo-S, cloΔ (⊆-closed cloA ext))
... | ind = ⊢lam₁ ind
t-⊆-prv (⊢lam₂ ⊢e up-c ⊢e₁) ext cloΔ =
  ⊢lam₂ (t-⊆-prv ⊢e ext cloΔ) up-c (t-⊆-prv ⊢e₁ (var ext) (clo-S, cloΔ (⊢closeA (t-⊆-prv ⊢e ext cloΔ))))
t-⊆-prv (⊢sub ⊢e ne gc cloΣ s) ext cloΔ =
  ⊢sub (t-⊆-prv ⊢e ext cloΔ) ne gc (⊆-closedᶜ cloΣ ext) (s-⊆-prv s (⊢closeA ⊢e) cloΣ ext)
t-⊆-prv (⊢tabs ⊢e) ext cloΔ = ⊢tabs (t-⊆-prv ⊢e (uvar ext) (clo-S∙ cloΔ))
