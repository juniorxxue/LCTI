module Implicit.Algo2Interm.AlgoCounter.Sound where

open import Implicit.Language.All
open import Implicit.Algo2Interm.AlgoCounter.Base
open import Implicit.Algo.All

-- counter based is sound
tc-sound : Γ ⊢ Σ ⇒ e ⇒ A ↡ j
         → Γ ⊢ Σ ⇒ e ⇒ A

sc-sound : Γ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B ↡ j
         → Γ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B

tc-sound (⊢lit regΓ) = ⊢lit regΓ
tc-sound (⊢var regΓ x∈Γ) = ⊢var regΓ x∈Γ
tc-sound (⊢ann ⊢e) = ⊢ann (tc-sound ⊢e)
tc-sound (⊢app ⊢e) = ⊢app (tc-sound ⊢e)
tc-sound (⊢lam₁ ⊢e) = ⊢lam₁ (tc-sound ⊢e)
tc-sound (⊢lam₂ ⊢e up-c ⊢e₁) = ⊢lam₂ (tc-sound ⊢e) up-c (tc-sound ⊢e₁)
tc-sound (⊢sub ⊢e ne gc s) = ⊢sub (tc-sound ⊢e) ne gc (sc-sound s)
tc-sound (⊢tabs ⊢e) = ⊢tabs (tc-sound ⊢e)
tc-sound {e = e ⓪ A} (⊢tapp s st) = ⊢tapp (tc-sound s) st

sc-sound (s-empty regΓ cloA x) = s-empty regΓ cloA x
sc-sound (s-type ss) = s-type ss
sc-sound (s-term-c nd s cloA ap ⊢e) = s-term-c nd (sc-sound s) cloA ap (tc-sound ⊢e)
sc-sound (s-term-o nd ⊢e ss s) = s-term-o nd (tc-sound ⊢e) ss (sc-sound s)
sc-sound (s-∀l-𝕚 s upᶜ upj upᵉ upC upD) = s-∀l (sc-sound s) upᶜ upᵉ upC upD
sc-sound (s-∀l-𝕔 s upᶜ upj upᵉ upC upD) = s-∀l (sc-sound s) upᶜ upᵉ upC upD
sc-sound (s-tapp s upᶜ upj) = s-tapp (sc-sound s) upᶜ

----------------------------------------------------------------------
--+                         useful lemmas                          +--
----------------------------------------------------------------------


tc-id0 : Γ ⊢ τ B ⇒ e ⇒ A ↡ j
       → B ≡ A
tc-id0 ⊢e = ⊢id0 (tc-sound ⊢e)

sc-⊆ : Γ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B ↡ j
     → Γ ⊆ Δ
sc-⊆ s = s-⊆ (sc-sound s)
