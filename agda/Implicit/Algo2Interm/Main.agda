module Implicit.Algo2Interm.Main where

open import Implicit.Language.All
open import Implicit.Interm.All
open import Implicit.Algo.All
open import Implicit.Algo2Interm.AlgoCounter.All
open import Implicit.Algo2Interm.Context2Counter
open import Implicit.Algo2Interm.Find


sound-ss : Γ ⊢ A ⌞ ≤ ⌝ B ⊣ Δ
         → Δ ⊢ ∞ # A ⌞ ≤ ⌝ B
sound-ss (s-int regΓ) = s-int regΓ
sound-ss (s-var-∙ regΓ x) = s-var-∙ regΓ x
sound-ss (s-ex-l^ inst) = s-svar-l (⊆-sregular' (inst-⊆ inst)) (inst-∋:= inst)
sound-ss (s-ex-r^ inst) = s-svar-r (⊆-sregular' (inst-⊆ inst)) (inst-∋:= inst)
sound-ss (s-ex-l= regΓ x-in) = s-svar-l regΓ x-in
sound-ss (s-ex-r= regΓ x-in) = s-svar-r regΓ x-in
sound-ss (s-arr s s₁) = s-arr₁ (s-⊆-prv (sound-ss s) (ss-⊆ s₁)) (sound-ss s₁)
sound-ss (s-∀ s) = s-∀ (sound-ss s)

----------------------------------------------------------------------
--+                           main logic                           +--
----------------------------------------------------------------------


tc-~ : Γ ⊢ Σ ⇒ e ⇒ A ↡ j
     → Γ ⊢ ⟨ j , A ⟩ ~t Σ

sc-~ : Γ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B ↡ j
     → Δ ⊢ ⟨ j , B ⟩ ~s Σ

sound : Γ ⊢ Σ ⇒ e ⇒ A ↡ j
      → Γ ⊢ j # e ⦂ A

sound-s : Γ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B ↡ j
        → Δ ⊢ j # A ⌞ ≤⁺ ⌝ B

tc-~ (⊢lit regΓ) = ~tZ
tc-~ (⊢var regΓ x∈Γ) = ~tZ
tc-~ (⊢ann ⊢e) = ~tZ
tc-~ (⊢app ⊢e) with tc-~ ⊢e
... | ~tI ⊢e₁ r = r
... | ~tC ⊢e₁ r = r
tc-~ (⊢lam₁ ⊢e) with tc-id0 ⊢e
... | refl = ~t∞
tc-~ (⊢lam₂ ⊢e up-c ⊢e₁) = ~tI (sound ⊢e) (~t-strengthen,0 (tc-~ ⊢e₁) up-c)
tc-~ (⊢sub ⊢e ne gc s) = ~s-~t (sc-~ s)
tc-~ (⊢tabs ⊢e) = ~tZ

sc-~ (s-empty regΓ cloA x) = ~sZ
sc-~ (s-type ss) = ~s∞
sc-~ (s-term-c cloA ap ⊢e s) with tc-id0 ⊢e
... | refl = ~sC (t-⊆-prv (sound ⊢e) (sc-⊆ s)) (sc-~ s)
sc-~ s'@(s-term-o opnA ⊢e ss s) = ~sI (t-⊆-prv (sound ⊢e) (sc-⊆ s')) (sc-~ s)
sc-~ (s-∀l s upᶜ upᵉ upC upD) = ~s-strengthen=0 (sc-~ s) (↑ty-arr upC upD) (↑tyᶜ-e upᵉ upᶜ)


sound (⊢lit regΓ) = ⊢lit regΓ
sound (⊢var regΓ x∈Γ) = ⊢var regΓ x∈Γ
sound (⊢ann ⊢e) with refl ← tc-id0 ⊢e = ⊢ann (sound ⊢e)
sound (⊢app ⊢e) with tc-~ ⊢e
... | ~tI ⊢e₁ r = ⊢app₂ (sound ⊢e) ⊢e₁
... | ~tC ⊢e₁ r = ⊢app₁ (sound ⊢e) ⊢e₁
sound (⊢lam₁ ⊢e) = ⊢lam₁ (sound ⊢e)
sound (⊢lam₂ ⊢e up-c ⊢e₁) = ⊢lam₂ (sound ⊢e₁)
sound (⊢sub ⊢e ne gc s) with sc-~ s
... | r = ⊢sub (sound ⊢e) (sound-s s) gc (NonEmpty-NonZ ne (~s-~t r))
sound (⊢tabs ⊢e) = ⊢tabs (sound ⊢e)

sound-s (s-empty regΓ cloA x) = s-refl regΓ cloA x
sound-s (s-type ss) = sound-ss ss
sound-s (s-term-c cloA ap ⊢e s) with tc-id0 ⊢e
... | refl = s-arr₃ (⊆-⊢c cloA (sc-⊆ s)) (⊆-⊢c-≫' (sc-⊆ s) cloA ap) (sound-s s)
sound-s (s-term-o opnA ⊢e ss s) = s-arr₂ (s-⊆-prv (sound-ss ss) (sc-⊆ s)) (sound-s s)
sound-s (s-∀l s upᶜ upᵉ upC upD) = s-∀l (sound-s s) (ic-aux (sc-~ s)) (s-find0 s upᵉ upᶜ) upC upD
    where ic-aux : Δ ,= B ⊢ ⟨ j , C `→ D ⟩ ~s [ e' ]↝ Σ'
                 → 𝕚𝕔 j
          ic-aux (~sI ⊢e s) = case-𝕚
          ic-aux (~sC ⊢e s) = case-𝕔
