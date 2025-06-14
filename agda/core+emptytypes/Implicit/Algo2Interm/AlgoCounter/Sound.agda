module Implicit.Algo2Interm.AlgoCounter.Sound where

open import Implicit.Language.All
open import Implicit.Algo2Interm.AlgoCounter.Base
open import Implicit.Algo.All

-- counter based is sound
tc-sound : Γ ⊢ Σ ⇒ e ⇒ A ↡ j
         → Γ ⊢ Σ ⇒ e ⇒ A

sc-sound : Γ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B ↡ j
         → Γ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B

infsc-sound : Γ ⊨ Σ ⟹ A ↡ j
            → Γ ⊨ Σ ⟹ A

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
sc-sound (s-term-c cloA ap ⊢e s) = s-term-c cloA ap (tc-sound ⊢e) (sc-sound s)
sc-sound (s-term-o opnA ⊢e ss s) = s-term-o opnA (tc-sound ⊢e) ss (sc-sound s)
sc-sound (s-∀l-𝕚 s upᶜ upj upᵉ upC upD) = s-∀l (sc-sound s) upᶜ upᵉ upC upD
sc-sound (s-∀l-𝕔 s upᶜ upj upᵉ upC upD) = s-∀l (sc-sound s) upᶜ upᵉ upC upD
sc-sound (s-tapp s upᶜ upj) = s-tapp (sc-sound s) upᶜ
sc-sound (s-svar-term inΓ s) = s-svar-term inΓ (sc-sound s)
sc-sound (s-svar-tapp inΓ s) = s-svar-tapp inΓ (sc-sound s)
sc-sound (s-∀l-no-𝕚 x upᶜ upj upᵉ upC upD) = s-∀l-no (sc-sound x) upᶜ upᵉ upC upD
sc-sound (s-∀l-no-𝕔 x upᶜ upj upᵉ upC upD) = s-∀l-no (sc-sound x) upᶜ upᵉ upC upD
sc-sound (s-evar-infers infs inst) = s-evar-infers (infsc-sound infs) inst

infsc-sound (infs-z regΓ regA) = infs-z regΓ regA
infsc-sound (infs-s ⊢e infs) = infs-s (tc-sound ⊢e) (infsc-sound infs)

----------------------------------------------------------------------
--+                         useful lemmas                          +--
----------------------------------------------------------------------


tc-id0 : Γ ⊢ τ B ⇒ e ⇒ A ↡ j
       → B ≡ A
tc-id0 ⊢e = ⊢id0 (tc-sound ⊢e)

sc-⊆ : Γ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B ↡ j
     → Γ ⊆ Δ
sc-⊆ s = s-⊆ (sc-sound s)

tc-⊢r : Γ ⊢ Σ ⇒ e ⇒ A ↡ j
      → Γ ⊢r A
tc-⊢r ⊢e = t-⊢r (tc-sound ⊢e)
