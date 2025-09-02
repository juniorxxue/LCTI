module Implicit.Algo.Properties.Regularity where

open import Implicit.Language.All
open import Implicit.Algo.Base
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
t-env (⊢tabs-τ ⊢e) with t-env ⊢e
... | reg-S∙ r = r
t-env (⊢tapp ⊢e st) = t-env ⊢e

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

ss-env-out : Γ ⊢ A ⌞ ≤ ⌝ B ⊣ Δ
           → SRegular Δ
ss-env-out s = ⊆-regular (ss-env-in s) (ss-⊆ s)

s-env-in : Γ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B
         → SRegular Γ
s-env-in (s-empty cloΓ cloA x) = cloΓ
s-env-in (s-type ss) = ss-env-in ss
s-env-in (s-term-c cloA ap ⊢e s) = s-env-in s
s-env-in (s-term-o opnA ⊢e x s) = ss-env-in x
s-env-in (s-tapp s upᶜ) with s-env-in s
... | reg-S= r regA = r
s-env-in (s-svar-term inΓ s) = s-env-in s
s-env-in (s-svar-tapp inΓ s) = s-env-in s
s-env-in (s-evar-infers x inst) = inst-env-in inst
s-env-in (s-∀l-y pk upB s upᶜ upᵉ upC upD) with s-env-in s
... | reg-S= r regA = r
s-env-in (s-∀l-n-y s upᶜ upᵉ upC upD) with s-env-in s
... | reg-S^ r = r
s-env-in (s-∀l-n-n s upᶜ upᵉ upC upD) with s-env-in s
... | reg-S^ r = r

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

----------------------------------------------------------------------
--+                              type                              +--
----------------------------------------------------------------------

infix 3 _⊢rᶜ_
data _⊢rᶜ_ : Env n m → Context n m → Set where
  ⊢rᶜ-empty : Γ ⊢rᶜ □
  ⊢rᶜ-τ : (regA : Γ ⊢r A)
        → Γ ⊢rᶜ (τ A)
  ⊢rᶜ-term : Γ ⊢rᶜ Σ
           → Γ ⊢rᶜ [ e ]↝ Σ
  ⊢rᶜ-tapp : (regA : Γ ⊢r A)
           → Γ ⊢rᶜ Σ
           → Γ ⊢rᶜ A ⓪↝ Σ

⊆-⊢rᶜ' : Δ ⊢rᶜ Σ
       → Γ ⊆ Δ
       → Γ ⊢rᶜ Σ
⊆-⊢rᶜ' ⊢rᶜ-empty ext = ⊢rᶜ-empty
⊆-⊢rᶜ' (⊢rᶜ-τ regA) ext = ⊢rᶜ-τ (⊆-⊢r' regA ext)
⊆-⊢rᶜ' (⊢rᶜ-term regΣ) ext = ⊢rᶜ-term (⊆-⊢rᶜ' regΣ ext)
⊆-⊢rᶜ' (⊢rᶜ-tapp regA regΓ) ext = ⊢rᶜ-tapp (⊆-⊢r' regA ext) (⊆-⊢rᶜ' regΓ ext)

⊢rᶜ-strengthen^0 : Γ ,^ ⊢rᶜ Σ'
                 → ↑tyᶜ0 Σ ⇘ Σ'
                 → Γ ⊢rᶜ Σ
⊢rᶜ-strengthen^0 ⊢rᶜ-empty ↑tyᶜ-□ = ⊢rᶜ-empty
⊢rᶜ-strengthen^0 (⊢rᶜ-τ regA) (↑tyᶜ-τ up-t) = ⊢rᶜ-τ (⊢r-strengthen^0 regA up-t)
⊢rᶜ-strengthen^0 (⊢rᶜ-term regΣ) (↑tyᶜ-e up-e upΣ) = ⊢rᶜ-term (⊢rᶜ-strengthen^0 regΣ upΣ)
⊢rᶜ-strengthen^0 (⊢rᶜ-tapp regA regΣ) (↑tyᶜ-⓪ upA upΣ) = ⊢rᶜ-tapp (⊢r-strengthen^0 regA upA) (⊢rᶜ-strengthen^0 regΣ upΣ)


⊢rᶜ-strengthen=0 : Γ ,= T ⊢rᶜ Σ'
                 → ↑tyᶜ0 Σ ⇘ Σ'
                 → Γ ⊢rᶜ Σ
⊢rᶜ-strengthen=0 ⊢rᶜ-empty ↑tyᶜ-□ = ⊢rᶜ-empty
⊢rᶜ-strengthen=0 (⊢rᶜ-τ regA) (↑tyᶜ-τ up-t) = ⊢rᶜ-τ (⊢r-strengthen=0 regA up-t)
⊢rᶜ-strengthen=0 (⊢rᶜ-term regΣ) (↑tyᶜ-e up-e upΣ) = ⊢rᶜ-term (⊢rᶜ-strengthen=0 regΣ upΣ)
⊢rᶜ-strengthen=0 (⊢rᶜ-tapp regA regΣ) (↑tyᶜ-⓪ upA upΣ) = ⊢rᶜ-tapp (⊢r-strengthen=0 regA upA) (⊢rᶜ-strengthen=0 regΣ upΣ)

⊢rᶜ-strengthen,0 : Γ , A ⊢rᶜ Σ'
                 → ↑tmᶜ0 Σ ⇘ Σ'
                 → Γ ⊢rᶜ Σ
⊢rᶜ-strengthen,0 ⊢rᶜ-empty ↑tmᶜ-□ = ⊢rᶜ-empty
⊢rᶜ-strengthen,0 (⊢rᶜ-τ regA) ↑tmᶜ-τ = ⊢rᶜ-τ (⊢r-strengthen,0 regA)
⊢rᶜ-strengthen,0 (⊢rᶜ-term regΣ) (↑tmᶜ-e up-e upΣ) = ⊢rᶜ-term (⊢rᶜ-strengthen,0 regΣ upΣ)
⊢rᶜ-strengthen,0 (⊢rᶜ-tapp regA regΣ) (↑tmᶜ-⓪ upΣ) = ⊢rᶜ-tapp (⊢r-strengthen,0 regA) (⊢rᶜ-strengthen,0 regΣ upΣ)

⊢rᶜ-⋈ : Γ ⋈ ⊢rᶜ Σ
      → Γ ⊢rᶜ Σ
⊢rᶜ-⋈ ⊢rᶜ-empty = ⊢rᶜ-empty
⊢rᶜ-⋈ (⊢rᶜ-τ regA) = ⊢rᶜ-τ (⊢r-𝕣' regA)
⊢rᶜ-⋈ (⊢rᶜ-term reg) = ⊢rᶜ-term (⊢rᶜ-⋈ reg)
⊢rᶜ-⋈ (⊢rᶜ-tapp regA regΓ) = ⊢rᶜ-tapp (⊢r-𝕣' regA) (⊢rᶜ-⋈ regΓ)

⊢rᶜ-𝕣 : 𝕣 Γ ⊢rᶜ Σ
      → Γ ⊢rᶜ Σ
⊢rᶜ-𝕣 ⊢rᶜ-empty = ⊢rᶜ-empty
⊢rᶜ-𝕣 (⊢rᶜ-τ regA) = ⊢rᶜ-τ (⊢r-𝕣 regA)
⊢rᶜ-𝕣 (⊢rᶜ-term regΣ) = ⊢rᶜ-term (⊢rᶜ-𝕣 regΣ)
⊢rᶜ-𝕣 (⊢rᶜ-tapp regA regΣ) = ⊢rᶜ-tapp (⊢r-𝕣 regA) (⊢rᶜ-𝕣 regΣ)

infs-⊢rᶜ : Γ ⊨ Σ ⟹ A
         → Γ ⊢rᶜ Σ
infs-⊢rᶜ (infs-z regΓ regA) = ⊢rᶜ-τ regA
infs-⊢rᶜ (infs-s x infs) = ⊢rᶜ-term (infs-⊢rᶜ infs)

s-⊢rᶜ : Γ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B
      → Γ ⊢rᶜ Σ
s-⊢rᶜ (s-empty regΓ cloA grd) = ⊢rᶜ-empty
s-⊢rᶜ (s-type ss) = ⊢rᶜ-τ (ss-polarity+ ss)
s-⊢rᶜ (s-term-c cloA ap ⊢e s) = ⊢rᶜ-term (s-⊢rᶜ s)
s-⊢rᶜ (s-term-o opnA ⊢e ss s) = ⊢rᶜ-term (⊆-⊢rᶜ' (s-⊢rᶜ s) (ss-⊆ ss))
s-⊢rᶜ (s-tapp s upᶜ) with s-env-in s
... | reg-S= r regA = ⊢rᶜ-tapp regA (⊢rᶜ-strengthen=0 (s-⊢rᶜ s) upᶜ)
s-⊢rᶜ (s-svar-term inΓ s) = s-⊢rᶜ s
s-⊢rᶜ (s-svar-tapp inΓ s) = s-⊢rᶜ s
s-⊢rᶜ (s-evar-infers tfs inst) with infs-⊢rᶜ tfs
... | ⊢rᶜ-term r = ⊢rᶜ-term (⊢rᶜ-𝕣 r)
s-⊢rᶜ (s-∀l-y pk upB s upᶜ upᵉ upC upD) with s-⊢rᶜ s
... | ⊢rᶜ-term r = ⊢rᶜ-term (⊢rᶜ-strengthen=0 r upᶜ)
s-⊢rᶜ (s-∀l-n-y s upᶜ upᵉ upC upD) with s-⊢rᶜ s
... | ⊢rᶜ-term r = ⊢rᶜ-term (⊢rᶜ-strengthen^0 r upᶜ)
s-⊢rᶜ (s-∀l-n-n s upᶜ upᵉ upC upD) with s-⊢rᶜ s
... | ⊢rᶜ-term r = ⊢rᶜ-term (⊢rᶜ-strengthen^0 r upᶜ)

t-⊢rᶜ : Γ ⊢ Σ ⇒ e ⇒ A
      → Γ ⊢rᶜ Σ
t-⊢rᶜ (⊢lit regΓ) = ⊢rᶜ-empty
t-⊢rᶜ (⊢var regΓ x∈Γ) = ⊢rᶜ-empty
t-⊢rᶜ (⊢ann ⊢e) = ⊢rᶜ-empty
t-⊢rᶜ (⊢app ⊢e) with t-⊢rᶜ ⊢e
... | ⊢rᶜ-term r = r
t-⊢rᶜ (⊢lam₁ ⊢e)
  with ⊢rᶜ-τ regA ← t-⊢rᶜ ⊢e
  with reg-S, regA' regΓ ← t-env ⊢e
  = ⊢rᶜ-τ (⊢r-arr regΓ (⊢r-strengthen,0 regA))
t-⊢rᶜ (⊢lam₂ ⊢e up-c ⊢e₁) = ⊢rᶜ-term (⊢rᶜ-strengthen,0 (t-⊢rᶜ ⊢e₁) up-c)
t-⊢rᶜ (⊢sub ⊢e ne gc s) = ⊢rᶜ-⋈ (s-⊢rᶜ s)
t-⊢rᶜ (⊢tabs ⊢e) = ⊢rᶜ-empty
t-⊢rᶜ (⊢tapp ⊢e st) with t-⊢rᶜ ⊢e
... | ⊢rᶜ-tapp regA regΓ = regΓ
t-⊢rᶜ (⊢tabs-τ ⊢e) with t-⊢rᶜ ⊢e
... | ⊢rᶜ-τ regA = ⊢rᶜ-τ (⊢r-∀ regA)

s-⊢r : Γ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B
     → Γ ⊢r B
t-⊢r : Γ ⊢ Σ ⇒ e ⇒ A
     → Γ ⊢r A
infs-⊢r : Γ ⊨ Σ ⟹ A
        → Γ ⊢r A

s-⊢r (s-empty regΓ cloA x) = ⊢c-≫-⊢r regΓ cloA x
s-⊢r (s-type ss) = ss-polarity+ ss
s-⊢r (s-term-c cloA ap ⊢e s) = ⊢r-arr (⊢c-≫-⊢r (s-env-in s) cloA ap) (s-⊢r s)
s-⊢r (s-term-o opnA ⊢e ss s) = ⊢r-arr (⊢r-𝕣 (t-⊢r ⊢e)) (⊆-⊢r' (s-⊢r s) (ss-⊆ ss))
s-⊢r (s-∀l-y pk upB s upᶜ upᵉ upC upD) = ⊢r-strengthen=0 (s-⊢r s) (↑ty-arr upC upD)
s-⊢r (s-∀l-n-y s upᶜ upᵉ upC upD) = ⊢r-strengthen^0 (s-⊢r s) (↑ty-arr upC upD)
s-⊢r (s-∀l-n-n s upᶜ upᵉ upC upD) = ⊢r-strengthen^0 (s-⊢r s) (↑ty-arr upC upD)
s-⊢r (s-tapp s upᶜ) = ⊢r-∀ (⊢r-◆0 (s-⊢r s))
s-⊢r (s-svar-term inΓ s) = s-⊢r s
s-⊢r (s-svar-tapp inΓ s) = s-⊢r s
s-⊢r (s-evar-infers tfs inst) = ⊢r-𝕣 (infs-⊢r tfs)

t-⊢r (⊢lit regΓ) = ⊢r-int
t-⊢r (⊢var regΓ x∈Γ) = ∋⦂-⊢r regΓ x∈Γ
t-⊢r (⊢ann ⊢e) with t-⊢rᶜ ⊢e
... | ⊢rᶜ-τ regA = regA
-- rewrite ⊢id0 ⊢e = t-⊢r ⊢e
t-⊢r (⊢app ⊢e) with t-⊢r ⊢e
... | ⊢r-arr r r₁ = r₁
t-⊢r (⊢lam₁ ⊢e) with t-env ⊢e
... | reg-S, r regA = ⊢r-arr regA (⊢r-strengthen,0 (t-⊢r ⊢e))
t-⊢r (⊢lam₂ ⊢e up-c ⊢e₁) = ⊢r-arr (t-⊢r ⊢e) (⊢r-strengthen,0 (t-⊢r ⊢e₁))
t-⊢r (⊢sub ⊢e ne gc s) = ⊢r-𝕣' (s-⊢r s)
t-⊢r (⊢tabs ⊢e) = ⊢r-∀ (t-⊢r ⊢e)
t-⊢r (⊢tapp ⊢e st) with t-⊢rᶜ ⊢e | t-⊢r ⊢e
... | ⊢rᶜ-tapp regA regΓ | ⊢r-∀ regB = ⊢r-strengthen∙0 regB st
t-⊢r (⊢tabs-τ ⊢e) = ⊢r-∀ (t-⊢r ⊢e)

infs-⊢r (infs-z regΓ regA) = regA
infs-⊢r (infs-s x infs) = ⊢r-arr (t-⊢r x) (infs-⊢r infs)

ss+-⊢c : Γ ⊢ A ⌞ ≤⁺ ⌝ B ⊣ Δ
       → Δ ⊢c A

ss--⊢c : Γ ⊢ A ⌞ ≤⁻ ⌝ B ⊣ Δ
       → Δ ⊢c B

ss+-⊢c (s-int regΓ) = ⊢c-int
ss+-⊢c (s-var-∙ regΓ inΔ) = ⊢c-var-∙ inΔ
ss+-⊢c (s-ex-l^ inst) = ⊢c-var-= (inst-∋= inst)
ss+-⊢c (s-ex-l= regΓ x-in) = ⊢c-var-= (∋:=to∋= x-in)
ss+-⊢c (s-arr s s₁) = ⊢c-arr (⊆-⊢c (ss--⊢c s) (ss-⊆ s₁)) (ss+-⊢c s₁)
ss+-⊢c (s-∀ s) = ⊢c-∀ (ss+-⊢c s)

ss--⊢c (s-int regΓ) = ⊢c-int
ss--⊢c (s-var-∙ regΓ inΔ) = ⊢c-var-∙ inΔ
ss--⊢c (s-ex-r^ inst) = ⊢c-var-= (inst-∋= inst)
ss--⊢c (s-ex-r= regΓ x-in) = ⊢c-var-= (∋:=to∋= x-in)
ss--⊢c (s-arr s s₁) = ⊢c-arr (⊆-⊢c (ss+-⊢c s) (ss-⊆ s₁)) (ss--⊢c s₁)
ss--⊢c (s-∀ s) = ⊢c-∀ (ss--⊢c s)

s-⊢c : Γ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B
     → Δ ⊢c A
s-⊢c (s-empty regΓ cloA grd) = cloA
s-⊢c (s-type ss) = ss+-⊢c ss
s-⊢c (s-term-c cloA ap ⊢e s) = ⊢c-arr (⊆-⊢c cloA (s-⊆ s)) (s-⊢c s)
s-⊢c (s-term-o opnA ⊢e ss s) = ⊢c-arr (⊆-⊢c (ss--⊢c ss) (s-⊆ s)) (s-⊢c s)
s-⊢c (s-∀l-y pk upB s upᶜ upᵉ upC upD) = ⊢c-∀ (⊢c-◆0 (s-⊢c s))
s-⊢c (s-∀l-n-y s upᶜ upᵉ upC upD) = ⊢c-∀ (⊢c-◆0 (s-⊢c s))
s-⊢c (s-∀l-n-n s upᶜ upᵉ upC upD) = ⊢c-∀ (⊢c-◇0 (s-⊢c s))
s-⊢c (s-tapp s upᶜ) = ⊢c-∀ (⊢c-◆0 (s-⊢c s))
s-⊢c (s-svar-term x s) = ⊢c-var-= (∋:=to∋= x)
s-⊢c (s-svar-tapp x s) = ⊢c-var-= (∋:=to∋= x)
s-⊢c (s-evar-infers infs inst) = ⊢c-var-= (inst-∋= inst)


----------------------------------------------------------------------
--+                           Extension                            +--
----------------------------------------------------------------------

s-⊆/ : Γ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B
     → Γ ⊆ Δ w/t A
s-⊆/ (s-empty regΓ cloA grd) = ⊆/-refl regΓ cloA
s-⊆/ (s-type ss) = ss+-⊆/ ss
s-⊆/ (s-term-c cloA ap ⊢e s) = ext-arr (⊆/-refl (s-env-in s) cloA) (s-⊆/ s)
s-⊆/ (s-term-o opnA ⊢e ss s) = ext-arr (ss--⊆/ ss) (s-⊆/ s)
s-⊆/ (s-∀l-y pk upB s upᶜ upᵉ upC upD) = ext-∀ (⊆/-◆◆0 (s-⊆/ s))
s-⊆/ (s-∀l-n-y s upᶜ upᵉ upC upD) = ext-∀ (⊆/-◇◆0 (s-⊆/ s))
s-⊆/ (s-∀l-n-n s upᶜ upᵉ upC upD) = ext-∀ (⊆/-◇◇0 (s-⊆/ s))
s-⊆/ (s-tapp s upᶜ) = ext-∀ (⊆/-◆◆0 (s-⊆/ s))
s-⊆/ (s-svar-term x s) = ⊆/-refl (s-env-in s) (⊢c-var-= (∋:=to∋= x))
s-⊆/ (s-svar-tapp x s) = ⊆/-refl (s-env-in s) (⊢c-var-= (∋:=to∋= x))
s-⊆/ (s-evar-infers infs inst) = ext-var (inst-⊆/x inst)
