module Implicit.AlgoCounter.Sound where

open import Implicit.Language.All
open import Implicit.AlgoCounter.Base
open import Implicit.Algo.Base

-- counter based is sound
tc-sound : Γ ⊢ Σ ⇒ e ⇒ A ↡ j
         → Γ ⊢ Σ ⇒ e ⇒ A

sc-sound : Γ ⊢ A ⌞ ≤ ⌝ Σ ⊣ Δ ↪ B ↡ j
         → Γ ⊢ A ⌞ ≤ ⌝ Σ ⊣ Δ ↪ B

tc-sound (⊢lit cloΓ) = ⊢lit cloΓ
tc-sound (⊢var cloΓ x∈Γ) = ⊢var cloΓ x∈Γ
tc-sound (⊢ann ⊢e) = ⊢ann (tc-sound ⊢e)
tc-sound (⊢app ⊢e) = ⊢app (tc-sound ⊢e)
tc-sound (⊢lam₁ ⊢e) = ⊢lam₁ (tc-sound ⊢e)
tc-sound (⊢lam₂ ⊢e up-c ⊢e₁) = ⊢lam₂ (tc-sound ⊢e) up-c (tc-sound ⊢e₁)
tc-sound (⊢sub ⊢e ne gc cloΣ s) = ⊢sub (tc-sound ⊢e) ne gc cloΣ (sc-sound s)
tc-sound (⊢tabs ⊢e) = ⊢tabs (tc-sound ⊢e)

sc-sound s-int = s-int
sc-sound (s-empty clo) = s-empty clo
sc-sound s-var = s-var
sc-sound (s-ex-l^ x-in inst) = s-ex-l^ x-in inst
sc-sound (s-ex-l= x-in s) = s-ex-l= x-in (sc-sound s)
sc-sound (s-ex-r^ x-in inst) = s-ex-r^ x-in inst
sc-sound (s-ex-r= x-in s) = s-ex-r= x-in (sc-sound s)
sc-sound (s-arr s s₁) = s-arr (sc-sound s) (sc-sound s₁)
sc-sound (s-term-c ⊢e s) = s-term-c (tc-sound ⊢e) (sc-sound s)
sc-sound (s-term-o opnA ⊢e s s₁) = s-term-o opnA (tc-sound ⊢e) (sc-sound s) (sc-sound s₁)
sc-sound (s-∀ s) = s-∀ (sc-sound s)
sc-sound (s-∀l s upᶜ upᵉ st₁ st₂) = s-∀l (sc-sound s) upᶜ upᵉ st₁ st₂
