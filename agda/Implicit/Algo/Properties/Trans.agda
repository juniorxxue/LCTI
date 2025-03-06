module Implicit.Algo.Properties.Trans where

open import Implicit.Language.All hiding (_⊆_)
open import Implicit.Algo.Base
open import Implicit.Algo.Properties.Id
open import Implicit.Algo.Properties.Shift
open import Implicit.Algo.Properties.Extension
open import Implicit.Algo.Properties.Weaken

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
ss-⊢r-eq+ (s-ex-l^ inst) (⊢r-var-∙ inΓ) = ⊥-elim {!!}
ss-⊢r-eq+ (s-ex-l= regΓ x-in) (⊢r-var-∙ inΓ) = ⊥-elim {!!}
ss-⊢r-eq+ (s-arr s s₁) (⊢r-arr regA regA₁)
  with refl ← ⊆-antisymm (ss-⊆ s) (ss-⊆ s₁)
  with refl ← ss-⊢r-eq- s regA
  with refl ← ss-⊢r-eq+ s₁ regA₁ = refl
ss-⊢r-eq+ (s-∀ s) (⊢r-∀ regA) with refl ← ss-⊢r-eq+ s regA = refl

s-trans : Γ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B
        → Δ ⊢ B ≤⁺ Σ' ⊣ Δ ↪ C
        → Σ ≊ Σ'
        → Γ ⊢ A ≤⁺ Σ' ⊣ Δ ↪ C
s-trans (s-empty cloΓ cloA x) (s-type ss) ≊Z = s-type {!!}
s-trans (s-term-c cloA ap ⊢e s1) (s-term-c cloA₁ ap₁ ⊢e₁ s2) (≊S newΣ) with ⊢id0 ⊢e | ⊢id0 ⊢e₁
... | refl | refl = s-term-c cloA {!!} {!!} (s-trans s1 s2 newΣ)
s-trans (s-term-c cloA ap ⊢e s1) (s-term-o opnA ⊢e₁ x s2) (≊S newΣ) = ⊥-elim {!!}
s-trans (s-term-o opnA ⊢e x s1) (s-term-c cloA ap ⊢e₁ s2) (≊S newΣ) = s-term-o opnA {!!} {!!} (s-trans s1 s2 newΣ)
s-trans (s-term-o opnA ⊢e x s1) (s-term-o opnA₁ ⊢e₁ x₁ s2) newΣ = ⊥-elim {!!}
s-trans (s-∀l s1 upᶜ upᵉ upC upD) s'@(s-term-c {A% = A%} {Σ = Σ′} {D = D} cloA ap ⊢e s2) (≊S newΣ) =
  let ⟨ Σ″ , upΣ′ ⟩ = ↑tyᶜ0-total Σ′
      ⟨ A%' , upA%' ⟩ = ↑ty0-total A%
      ⟨ D' , upD' ⟩ = ↑ty0-total D
  in s-∀l (s-trans s1 (s-weaken=0 s' (↑ty-arr upC upD) (↑tyᶜ-e upᵉ upΣ′) (↑ty-arr upA%' upD')) (≊S {!!})) upΣ′ upᵉ upA%' upD'
s-trans (s-∀l s1 upᶜ upᵉ upC upD) (s-term-o opnA ⊢e x s2) (≊S newΣ) = ⊥-elim {!!}
