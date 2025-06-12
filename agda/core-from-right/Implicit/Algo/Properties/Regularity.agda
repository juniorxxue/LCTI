{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --allow-incomplete-matches #-}
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

ss-env-in : Γ ⊢ A ⌞ ≤ ⌝ B ⊣ Δ
          → SRegular Γ
ss-env-in (s-int regΓ) = regΓ
ss-env-in (s-var-∙ regΓ x) = regΓ
ss-env-in (s-ex-l^ inst) = inst-env-in inst
ss-env-in (s-ex-r^ inst) = inst-env-in inst
ss-env-in (s-ex-l= regΓ x-in) = regΓ
ss-env-in (s-ex-r= regΓ x-in) = regΓ
ss-env-in (s-arr s s₁) = ss-env-in s₁
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
s-env-in (s-term-o opnA ⊢e x s) = s-env-in s
s-env-in (s-∀l s upᶜ upᵉ upC upD) with s-env-in s
... | reg-S^ r = r
s-env-in (s-∀l-no s upᶜ upᵉ upC upD) with s-env-in s
... | reg-S^ r = r
s-env-in (s-tapp s upᶜ) with s-env-in s
... | reg-S= r regA = r

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


s-⊢rᶜ : Γ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B
      → Γ ⊢rᶜ Σ
s-⊢rᶜ (s-empty regΓ cloA grd) = ⊢rᶜ-empty
s-⊢rᶜ (s-type ss) = ⊢rᶜ-τ (ss-polarity+ ss)
s-⊢rᶜ (s-term-c cloA ap ⊢e s) = ⊢rᶜ-term (s-⊢rᶜ s)
s-⊢rᶜ (s-term-o opnA ⊢e ss s) = {!!}
-- ⊢rᶜ-term (⊆-⊢rᶜ' (s-⊢rᶜ s) (ss-⊆ ss))
s-⊢rᶜ (s-∀l s upᶜ upᵉ upC upD) with s-⊢rᶜ s
... | ⊢rᶜ-term r = ⊢rᶜ-term (⊢rᶜ-strengthen^0 r upᶜ)
s-⊢rᶜ (s-∀l-no s upᶜ upᵉ upC upD) with s-⊢rᶜ s
... | ⊢rᶜ-term r = ⊢rᶜ-term (⊢rᶜ-strengthen^0 r upᶜ)
s-⊢rᶜ (s-tapp s upᶜ) with s-env-in s
... | reg-S= r regA = ⊢rᶜ-tapp regA (⊢rᶜ-strengthen=0 (s-⊢rᶜ s) upᶜ)

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

s-⊢r : Γ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B
     → Γ ⊢r B
t-⊢r : Γ ⊢ Σ ⇒ e ⇒ A
     → Γ ⊢r A

s-⊢r (s-empty regΓ cloA x) = ⊢c-≫-⊢r regΓ cloA x
s-⊢r (s-type ss) = ss-polarity+ ss
s-⊢r (s-term-c cloA ap ⊢e s) = ⊢r-arr (⊆-⊢r' (⊢c-≫-⊢r (s-env-out s) cloA ap) (s-⊆ s)) (s-⊢r s)
s-⊢r (s-term-o opnA ⊢e ss s) = ⊢r-arr {!!} {!!}
s-⊢r (s-∀l s upᶜ upᵉ upC upD) = ⊢r-strengthen^0 (s-⊢r s) (↑ty-arr upC upD)
s-⊢r (s-∀l-no s upᶜ upᵉ upC upD) = ⊢r-strengthen^0 (s-⊢r s) (↑ty-arr upC upD)
s-⊢r (s-tapp s upᶜ) = ⊢r-∀ (⊢r-◆0 (s-⊢r s))


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
t-⊢r (⊢tapp ⊢e st) with t-⊢rᶜ ⊢e
... | ⊢rᶜ-tapp regA regΓ = st0-⊢r (t-⊢r ⊢e) regA st


----------------------------------------------------------------------
--+                           Extension                            +--
----------------------------------------------------------------------

{- this lemma is correct and provable
   but requires several irrevelence lemmas, but is heavy to prove, thus avoid this lemma in its call site
s-⊆/ : Γ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B
     → Γ ⊆ Δ w/t A
s-⊆/ (s-empty regΓ cloA grd) = ⊆/-refl regΓ cloA
s-⊆/ (s-type ss) = ss+-⊆/ ss
s-⊆/ (s-term-c cloA ap ⊢e s) = ext-arr (⊆/-refl (s-env-in s) cloA) (s-⊆/ s)
s-⊆/ (s-term-o opnA ⊢e ss s) = ext-arr (ss--⊆/ ss) (s-⊆/ s)
s-⊆/ (s-∀l s upᶜ upᵉ upC upD) = ext-∀ {!s-⊆/ s!}
s-⊆/ (s-∀l-no s upᶜ upᵉ upC upD) = ext-∀ {!s-⊆/ s!}
s-⊆/ (s-tapp s upᶜ) = ext-∀ {!s-⊆/ s!}
s-⊆/ (s-svar-term x s) = ⊆/-refl (s-env-in s) (⊢c-var-= (∋:=to∋= x))
s-⊆/ (s-svar-tapp x s) = ⊆/-refl (s-env-in s) (⊢c-var-= (∋:=to∋= x))
-}
