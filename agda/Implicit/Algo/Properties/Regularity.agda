module Implicit.Algo.Properties.Regularity where

open import Implicit.Language.All
open import Implicit.Algo.Base
open import Implicit.Algo.Properties.Id
open import Implicit.Algo.Properties.Extension
open import Implicit.Algo.Properties.Polarity

----------------------------------------------------------------------
--+                          environments                          +--
----------------------------------------------------------------------

t-env : Γ ⊢ Σ ⇒ e ⇒ A
      → TRegular Γ
t-env (⊢lit regΓ) = regΓ
t-env (⊢var regΓ x∈Γ) = regΓ
t-env (⊢ann ⊢e) = t-env ⊢e
t-env (⊢app ⊢e) = t-env ⊢e
t-env (⊢lam₁ ⊢e) with t-env ⊢e
... | reg-S, r regA = r
t-env (⊢lam₂ ⊢e up-c ⊢e₁) = t-env ⊢e
t-env (⊢sub ⊢e ne gc s) = t-env ⊢e
t-env (⊢tabs ⊢e) with t-env ⊢e
... | reg-S∙ r = r
t-env (⊢tapp ⊢e st) = t-env ⊢e

inst-env-in : [ A / X ] Γ ⟹ Δ
            → SRegular Γ
inst-env-in (⟹^0 up regA env) = reg-S^ env
inst-env-in (⟹^S inst up1) = reg-S^ (inst-env-in inst)
inst-env-in (⟹∙S inst up1) = reg-S∙ (inst-env-in inst)
inst-env-in (⟹=S inst up1 regB) = reg-S= (inst-env-in inst) regB
inst-env-in (⟹≝S inst up1 regB) = reg-S≝ (inst-env-in inst) regB

ss-env-in : Γ ⊢ A ⌞ ≤ ⌝ B ⊣ Δ
          → SRegular Γ
ss-env-in (s-int regΓ) = regΓ
ss-env-in (s-var-∙ regΓ x) = regΓ
ss-env-in (s-ex-l^ inst) = inst-env-in inst
ss-env-in (s-ex-r^ inst) = inst-env-in inst
ss-env-in (s-ex-l= regΓ x-in) = regΓ
ss-env-in (s-ex-r= regΓ x-in) = regΓ
ss-env-in (s-arr s s₁) = ss-env-in s
ss-env-in (s-∀ s) with ss-env-in s
... | reg-S∙ r = r
ss-env-in (s-var-≝ regΓ x) = regΓ
ss-env-in (s-def-l= regΓ x-in) = regΓ
ss-env-in (s-def-r= regΓ x-in) = regΓ

ss-env-out : Γ ⊢ A ⌞ ≤ ⌝ B ⊣ Δ
           → SRegular Δ
ss-env-out s = ⊆-regular (ss-env-in s) (ss-⊆ s)

s-env-in : Γ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B
         → SRegular Γ
s-env-in (s-empty cloΓ cloA x) = cloΓ
s-env-in (s-type ss) = ss-env-in ss
s-env-in (s-term-c cloA ap ⊢e s) = s-env-in s
s-env-in (s-term-o opnA ⊢e x s) = ss-env-in x
s-env-in (s-∀l s upᶜ upᵉ upC upD) with s-env-in s
... | reg-S^ r = r
s-env-in (s-tapp s upᶜ) with s-env-in s
... | reg-S≝ r regA = r

s-env-out : Γ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B
          → SRegular Δ
s-env-out s = ⊆-regular (s-env-in s) (s-⊆ s)

inst-env-out : [ A / X ] Γ ⟹ Δ
             → SRegular Δ
inst-env-out (⟹^0 up regA env) = reg-S= env regA
inst-env-out (⟹^S inst up1) = reg-S^ (inst-env-out inst)
inst-env-out (⟹∙S inst up1) = reg-S∙ (inst-env-out inst)
inst-env-out (⟹=S inst up1 regB) with inst-env-out inst
... | r = reg-S= r (⊆-⊢r regB (inst-⊆ inst))
inst-env-out (⟹≝S inst up1 regB) with inst-env-out inst
... | r = reg-S≝ r (⊆-⊢r regB (inst-⊆ inst))

----------------------------------------------------------------------
--+                              type                              +--
----------------------------------------------------------------------

s-⊢r : Γ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B
     → Γ ⊢r B

postulate
  t-⊢r : Γ ⊢ Σ ⇒ e ⇒ A
     → Γ ⊢r A

s-⊢r (s-empty regΓ cloA x) = ⊢c-≫-⊢r regΓ cloA x
s-⊢r (s-type ss) = ss-polarity+ ss
s-⊢r (s-term-c cloA ap ⊢e s) = ⊢r-arr (⊢c-≫-⊢r (s-env-in s) cloA ap) (s-⊢r s)
s-⊢r (s-term-o opnA ⊢e ss s) = ⊢r-arr (⊢r-𝕣 (t-⊢r ⊢e)) (⊆-⊢r' (s-⊢r s) (ss-⊆ ss))
s-⊢r (s-∀l s upᶜ upᵉ upC upD) = ⊢r-strengthen^0 (s-⊢r s) (↑ty-arr upC upD)
s-⊢r (s-tapp x upᶜ) = ⊢r-∀ (⊢r-≝-∙0 (s-⊢r x))

{-
t-⊢r (⊢lit regΓ) = ⊢r-int
t-⊢r (⊢var regΓ x∈Γ) = ∋⦂-⊢r regΓ x∈Γ
t-⊢r (⊢ann ⊢e) rewrite ⊢id0 ⊢e = t-⊢r ⊢e
t-⊢r (⊢app ⊢e) with t-⊢r ⊢e
... | ⊢r-arr r r₁ = r₁
t-⊢r (⊢lam₁ ⊢e) with t-env ⊢e
... | reg-S, r regA = ⊢r-arr regA (⊢r-strengthen,0 (t-⊢r ⊢e))
t-⊢r (⊢lam₂ ⊢e up-c ⊢e₁) = ⊢r-arr (t-⊢r ⊢e) (⊢r-strengthen,0 (t-⊢r ⊢e₁))
t-⊢r (⊢sub ⊢e ne gc s) = ⊢r-𝕣' (s-⊢r s)
t-⊢r (⊢tabs ⊢e) = ⊢r-∀ (t-⊢r ⊢e)
t-⊢r {e = e ⓪ A} (⊢tapp x st) = st0-⊢r (t-⊢r x) {!!} st
-}
