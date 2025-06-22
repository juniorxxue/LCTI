module Implicit.Algo.Properties.Trans where

open import Implicit.Language.All
open import Implicit.Algo.Base
open import Implicit.Algo.Properties.Id
open import Implicit.Algo.Properties.Shift
open import Implicit.Algo.Properties.Extension
open import Implicit.Algo.Properties.Weaken
open import Implicit.Algo.Properties.Regularity
open import Implicit.Algo.Properties.Polarity


≊-↑ty0 : Σ₁ ≊ Σ₂
       → ↑tyᶜ0 Σ₁ ⇘ Σ₁'
       → ↑tyᶜ0 Σ₂ ⇘ Σ₂'
       → Σ₁' ≊ Σ₂'
≊-↑ty0 ≊Z ↑tyᶜ-□ (↑tyᶜ-τ up-t) = ≊Z
≊-↑ty0 (≊S newΣ) (↑tyᶜ-e up-e up1) (↑tyᶜ-e up-e₁ up2) with refl ← ↑tyᵉ-unique up-e up-e₁ = ≊S (≊-↑ty0 newΣ up1 up2)
≊-↑ty0 (≊⓪ newΣ) (↑tyᶜ-⓪ x up1) (↑tyᶜ-⓪ x₁ up2)
  with refl ← ↑ty-unique x₁ x = ≊⓪ (≊-↑ty0 newΣ up1 up2)


ss-grd+ : SRegular Γ
       → Γ ⊢c A
         → Γ ≫ A ⇘ B
         → Γ ⊢ A ⌞ ≤⁺ ⌝ B ⊣ Γ
ss-grd- : SRegular Γ
       → Γ ⊢c A
         → Γ ≫ A ⇘ B
         → Γ ⊢ B ⌞ ≤⁻ ⌝ A ⊣ Γ

ss-grd+ regΓ cloA grd-int = s-int regΓ
ss-grd+ regΓ cloA (grd-var= x) = s-ex-l= regΓ x
ss-grd+ regΓ cloA (grd-var∙ x) = s-var-∙ regΓ x
ss-grd+ regΓ (⊢c-arr cloA cloA₁) (grd-arr grd grd₁) = s-arr (ss-grd- regΓ cloA grd) (ss-grd+ regΓ cloA₁ grd₁)
ss-grd+ regΓ (⊢c-∀ cloA) (grd-∀ grd) = s-∀ (ss-grd+ (reg-S∙ regΓ) cloA grd)

ss-grd- regΓ cloA grd-int = s-int regΓ
ss-grd- regΓ cloA (grd-var= x) = s-ex-r= regΓ x
ss-grd- regΓ cloA (grd-var∙ x) = s-var-∙ regΓ x
ss-grd- regΓ (⊢c-arr cloA cloA₁) (grd-arr grd grd₁) = s-arr (ss-grd+ regΓ cloA grd) (ss-grd- regΓ cloA₁ grd₁)
ss-grd- regΓ (⊢c-∀ cloA) (grd-∀ grd) = s-∀ (ss-grd- (reg-S∙ regΓ) cloA grd)

ss-⊢r-eq+ : Γ ⊢ A ⌞ ≤⁺ ⌝ B ⊣ Γ
          → Γ ⊢r A
          → A ≡ B

ss-⊢r-eq- : Γ ⊢ A ⌞ ≤⁻ ⌝ B ⊣ Γ
          → Γ ⊢r B
           → A ≡ B

ss-⊢r-eq+ (s-int regΓ) regA = refl
ss-⊢r-eq+ (s-var-∙ regΓ x) regA = refl
ss-⊢r-eq+ (s-ex-l^ inst) (⊢r-var-∙ inΓ) = ⊥-elim (∋^-∋∙-false (inst-∋^ inst) inΓ)
ss-⊢r-eq+ (s-ex-l= regΓ x-in) (⊢r-var-∙ inΓ) = ⊥-elim (∋∙-∋:=-false inΓ x-in)
ss-⊢r-eq+ (s-arr s s₁) (⊢r-arr regA regA₁)
  with refl ← ⊆-antisymm (ss-⊆ s) (ss-⊆ s₁)
  with refl ← ss-⊢r-eq- s regA
  with refl ← ss-⊢r-eq+ s₁ regA₁ = refl
ss-⊢r-eq+ (s-∀ s) (⊢r-∀ regA) with refl ← ss-⊢r-eq+ s regA = refl
ss-⊢r-eq+ (s-arr-n s s₁) (⊢r-arr regA regA₁)
  with refl ← ⊆-antisymm (ss-⊆ s) (ss-⊆ s₁)
  with refl ← ss-⊢r-eq- s₁ regA
  with refl ← ss-⊢r-eq+ s regA₁ = refl

ss-⊢r-eq- (s-int regΓ) regA = refl
ss-⊢r-eq- (s-var-∙ regΓ x) regA = refl
ss-⊢r-eq- (s-ex-r^ inst) (⊢r-var-∙ inΓ) = ⊥-elim (∋^-∋∙-false (inst-∋^ inst) inΓ)
ss-⊢r-eq- (s-ex-r= regΓ x-in) (⊢r-var-∙ inΓ) = ⊥-elim (∋∙-∋:=-false inΓ x-in)
ss-⊢r-eq- (s-arr s s₁) (⊢r-arr regA regA₁)
  with refl ← ⊆-antisymm (ss-⊆ s) (ss-⊆ s₁) = cong₂ _`→_ (sym (ss-⊢r-eq+ s regA)) (ss-⊢r-eq- s₁ regA₁)
ss-⊢r-eq- (s-∀ s) (⊢r-∀ regA) = cong `∀_ (ss-⊢r-eq- s regA)
ss-⊢r-eq- (s-arr-n s s₁) (⊢r-arr regA regA₁)
  with refl ← ⊆-antisymm (ss-⊆ s) (ss-⊆ s₁) = cong₂ _`→_ (sym (ss-⊢r-eq+ s₁ regA)) (ss-⊢r-eq- s regA₁)

s-trans : Γ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B
        → Δ ⊢ B ≤⁺ Σ' ⊣ Δ ↪ C
        → Σ ≊ Σ'
        → Γ ⊢ A ≤⁺ Σ' ⊣ Δ ↪ C
s-trans (s-empty regΓ cloA grd) (s-type ss) ≊Z with ss-⊢r-eq+ ss (⊢c-≫-⊢r regΓ cloA grd)
... | refl = s-type (ss-grd+ regΓ cloA grd)
s-trans (s-term-c ap ⊢e s1) (s-term-c ap₁ ⊢e₁ s2) newΣ = {!!}
s-trans (s-term-c ap ⊢e s1) (s-term-c-n s2 ap₁ ⊢e₁) newΣ = {!!}
s-trans (s-term-c ap ⊢e s1) (s-term-o ⊢e₁ ss s2) (≊S newΣ) = {!!}
s-trans (s-term-c ap ⊢e s1) (s-term-o-n s2 ⊢e₁ ss) newΣ = {!!}
s-trans (s-term-c-n s1 ap ⊢e) s2 newΣ = {!!}
s-trans (s-term-o ⊢e ss s1) s2 newΣ = {!!}
s-trans (s-term-o-n s1 ⊢e ss) s2 newΣ = {!!}
s-trans (s-∀l s1 upᶜ upᵉ upC upD) s2 newΣ = {!!}
s-trans (s-∀l-no s1 upᶜ upᵉ upC upD) s2 newΣ = {!!}
s-trans (s-tapp s1 upᶜ) s2 newΣ = {!!}
s-trans (s-svar-term x s1) s2 newΣ = {!!}
s-trans (s-svar-tapp x s1) s2 newΣ = {!!}
s-trans (s-evar-infers infs inst) s2 newΣ = {!!}
