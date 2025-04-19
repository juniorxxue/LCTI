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

ss-⊢r-eq- (s-int regΓ) regA = refl
ss-⊢r-eq- (s-var-∙ regΓ x) regA = refl
ss-⊢r-eq- (s-ex-r^ inst) (⊢r-var-∙ inΓ) = ⊥-elim (∋^-∋∙-false (inst-∋^ inst) inΓ)
ss-⊢r-eq- (s-ex-r= regΓ x-in) (⊢r-var-∙ inΓ) = ⊥-elim (∋∙-∋:=-false inΓ x-in)
ss-⊢r-eq- (s-arr s s₁) (⊢r-arr regA regA₁)
  with refl ← ⊆-antisymm (ss-⊆ s) (ss-⊆ s₁) = cong₂ _`→_ (sym (ss-⊢r-eq+ s regA)) (ss-⊢r-eq- s₁ regA₁)
ss-⊢r-eq- (s-∀ s) (⊢r-∀ regA) = cong `∀_ (ss-⊢r-eq- s regA)

s-trans : Γ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B
        → Δ ⊢ B ≤⁺ Σ' ⊣ Δ ↪ C
        → Σ ≊ Σ'
        → Γ ⊢ A ≤⁺ Σ' ⊣ Δ ↪ C
s-trans (s-empty regΓ cloA grd) (s-type ss) ≊Z = {!!}
s-trans (s-term-c x s1 cloA ap ⊢e) (s-term-c x₁ s2 cloA₁ ap₁ ⊢e₁) (≊S new) = {!!}
s-trans (s-term-c x s1 cloA ap ⊢e) (s-term-o x₁ ⊢e₁ ss s2) (≊S new) = ⊥-elim {!!}
s-trans (s-term-o x ⊢e ss s1) (s-term-c nd s2 cloA ap ⊢e₁) (≊S new) = ⊥-elim {!!}
s-trans (s-term-o x ⊢e ss s1) (s-term-o nd ⊢e₁ ss₁ s2) (≊S new) = s-term-o x {!!} {!!} (s-trans s1 {!!} {!!})
s-trans (s-∀l s1 upᶜ upᵉ upC upD) s2 new = {!!}
s-trans (s-tapp s1 upᶜ) s2 new = {!!}


{-
  with reg-S= regΓ regB ← s-env-out s1
  with ⟨ Σ″ , upΣ′ ⟩ ← ↑tyᶜ0-total Σ'
  with ⟨ B' , upB' ⟩ ← ↑ty0-total B
  with ⟨ C' , upC' ⟩ ← ↑ty0-total C
  with ih ← s-trans s1 (s-weaken=0 s2 upC {!!} {!!} regB) (≊-↑ty0 newΣ upᶜ upΣ′)
  = s-tapp ih {!!} {!!}
-- we cannot copy forall-L solution, since tapp with eliminate the context, while forall-L doesn't
-}
