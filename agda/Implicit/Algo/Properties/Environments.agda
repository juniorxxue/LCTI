module Implicit.Algo.Properties.Environments where

open import Implicit.Language.All
open import Implicit.Algo.Base

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

inst-env-in : [ A / X ] Γ ⟹ Δ
            → SRegular Γ
inst-env-in (⟹^0 up regA env) = reg-S^ env
inst-env-in (⟹^S inst up1) = reg-S^ (inst-env-in inst)
inst-env-in (⟹∙S inst up1) = reg-S∙ (inst-env-in inst)
inst-env-in (⟹=S inst up1 regB) = reg-S= (inst-env-in inst) regB

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

s-env-in : Γ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B
         → SRegular Γ
s-env-in (s-empty cloΓ cloA x) = cloΓ
s-env-in (s-type ss) = ss-env-in ss
s-env-in (s-term-c cloA ap ⊢e s) = s-env-in s
s-env-in (s-term-o opnA ⊢e x s) = ss-env-in x
s-env-in (s-∀l s upᶜ upᵉ upC upD) with s-env-in s
... | reg-S^ r = r


inst-env-out : [ A / X ] Γ ⟹ Δ
             → SRegular Δ
inst-env-out (⟹^0 up regA env) = reg-S= env regA
inst-env-out (⟹^S inst up1) = reg-S^ (inst-env-out inst)
inst-env-out (⟹∙S inst up1) = reg-S∙ (inst-env-out inst)
inst-env-out (⟹=S inst up1 regB) with inst-env-out inst
... | r = reg-S= r {!!}
