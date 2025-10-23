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

abstract
  s-trans : Γ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B
        → Δ ⊢ B ≤⁺ Σ' ⊣ Δ ↪ C
        → Σ ≊ Σ'
        → Γ ⊢ A ≤⁺ Σ' ⊣ Δ ↪ C
  s-trans (s-empty cloΓ cloA x) (s-type ss) ≊Z with ss-⊢r-eq+ ss (⊢c-≫-⊢r cloΓ cloA x)
  ... | refl = s-type (ss-grd+ cloΓ cloA x)
  s-trans (s-term-c cloA ap ⊢e s1) (s-term-c cloA₁ ap₁ ⊢e₁ s2) (≊S newΣ)
    with regA% ← ⊢c-≫-⊢r (s-env-in s1) cloA ap
    with relf ← ⊢id0 ⊢e
    with refl ← ⊢id0 ⊢e₁
    with refl ← ⊢r-≫-eq' (⊆-⊢r regA% (s-⊆ s1)) ap₁ = s-term-c cloA ap ⊢e (s-trans s1 s2 newΣ)
  s-trans (s-term-c cloA ap ⊢e s1) (s-term-o opnA ⊢e₁ x s2) (≊S newΣ) = let regA = ⊆-⊢r (⊢c-≫-⊢r (s-env-in s1) cloA ap) (s-⊆ s1)
                                                                      in ⊥-elim (⊢r-⊢o-false regA opnA)
  s-trans s'@(s-term-o opnA ⊢e x s1) (s-term-c cloA ap ⊢e₁ s2) (≊S newΣ)
    with refl ← ⊢r-≫-eq' (⊆-⊢r (ss-polarity- x) (s-⊆ s')) ap = s-term-o opnA ⊢e x (s-trans s1 s2 newΣ)
  s-trans s'@(s-term-o opnA ⊢e x s1) (s-term-o opnA₁ ⊢e₁ x₁ s2) (≊S newΣ) = let regA = ⊆-⊢r (⊢r-𝕣 (t-⊢r ⊢e)) (s-⊆ s')
                                                                            in ⊥-elim (⊢r-⊢o-false regA opnA₁)
  s-trans (s-∀l s1 upᶜ upᵉ upC upD) s'@(s-term-c {A% = A%} {Σ = Σ′} {D = D} cloA ap ⊢e s2) (≊S newΣ)
    with reg-S= regΓ regB ← s-env-out s1
    = let ⟨ Σ″ , upΣ′ ⟩ = ↑tyᶜ0-total Σ′
          ⟨ A%' , upA%' ⟩ = ↑ty0-total A%
          ⟨ D' , upD' ⟩ = ↑ty0-total D
      in s-∀l (s-trans s1 (s-weaken=0 s' (↑ty-arr upC upD) (↑tyᶜ-e upᵉ upΣ′) (↑ty-arr upA%' upD') regB) (≊S (≊-↑ty0 newΣ upᶜ upΣ′))) upΣ′ upᵉ upA%' upD'
  s-trans s'@(s-∀l s1 upᶜ upᵉ upC upD) (s-term-o opnA ⊢e x s2) (≊S newΣ)
    with (⊢r-arr regC regD) ← s-⊢r s' = let regA = ⊆-⊢r regC (s-⊆ s') in ⊥-elim (⊢r-⊢o-false regA opnA)
  s-trans (s-∀l-no s1 upᶜ upᵉ upC upD) s'@(s-term-c {A% = A%} {Σ = Σ′} {D = D} cloA ap ⊢e s2) (≊S newΣ)
    with reg-S^ regB ← s-env-out s1
    = let ⟨ Σ″ , upΣ′ ⟩ = ↑tyᶜ0-total Σ′
          ⟨ A%' , upA%' ⟩ = ↑ty0-total A%
          ⟨ D' , upD' ⟩ = ↑ty0-total D
      in s-∀l-no (s-trans s1 (s-weaken^0 s' (↑ty-arr upC upD)
                                         (↑tyᶜ-e upᵉ upΣ′) (↑ty-arr upA%' upD')) (≊S (≊-↑ty0 newΣ upᶜ upΣ′))) upΣ′ upᵉ upA%' upD'
  s-trans s'@(s-∀l-no s1 upᶜ upᵉ upC upD) (s-term-o opnA ⊢e x s2) (≊S newΣ)
    with (⊢r-arr regC regD) ← s-⊢r s' = let regA = ⊆-⊢r regC (s-⊆ s') in ⊥-elim (⊢r-⊢o-false regA opnA)
  s-trans (s-svar-term inΓ s) (s-term-c cloA ap ⊢e s2) (≊S newΣ) = s-svar-term inΓ (s-trans s (s-term-c cloA ap ⊢e s2) (≊S newΣ))
  s-trans (s-svar-term inΓ s) (s-term-o opnA ⊢e ss s2) (≊S newΣ)
    with ⊢r-arr regA regB ← s-⊢r s = ⊥-elim (⊢r-⊢o-false regA opnA)
  s-trans (s-evar-infers (infs-s x infs) inst) s2 (≊S newΣ) = ⊥-elim (≊-infs-false infs newΣ)
          where ≊-infs-false : Γ ⊨ Σ ⟹ A
                             → Σ ≊ Σ'
                             → ⊥
                ≊-infs-false (infs-s x infs) (≊S newΣ) = ≊-infs-false infs newΣ
