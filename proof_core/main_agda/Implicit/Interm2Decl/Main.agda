module Implicit.Interm2Decl.Main where

open import Implicit.Language.All
import Implicit.Decl.All as D
import Implicit.Interm.All as I
open import Implicit.Decl.All
open import Implicit.Interm.All

sd-strengthen= : Γ ⊢d² j' # A' ≤ B'
               → Γ ◀ k =⇘ Γ'
               → A ↑ty k ⇘ A'
               → B ↑ty k ⇘ B'
               → j ↑tyʲ k ⇘ j'
               → Γ' ⊢d² j # A ≤ B
sd-strengthen= (s-refl regΔ cloA) new upA upB ↑tyʲ-Z
  with refl ← ↑ty-unique-inver upA upB
  = s-refl (sregular-strengthen= regΔ new) (⊢r-strengthen= cloA new upB)
sd-strengthen= (s-int regΔ) new ↑ty-int ↑ty-int ↑tyʲ-∞ = s-int (sregular-strengthen= regΔ new)
sd-strengthen= {B = ‶ X} (s-var-∙ regΔ inΔ) new ↑ty-var upB ↑tyʲ-∞
  with refl ← ↑ty-var-inv upB refl = s-var-∙ (sregular-strengthen= regΔ new) (∋∙-strengthen= inΔ new)
sd-strengthen= (s-arr₁ s s₁) new (↑ty-arr upA upA₁) (↑ty-arr upB upB₁) ↑tyʲ-∞
  = s-arr₁ (sd-strengthen= s new upB upA ↑tyʲ-∞) (sd-strengthen= s₁ new upA₁ upB₁ ↑tyʲ-∞)
sd-strengthen= (s-arr₂ s s₁) new (↑ty-arr upA upA₁) (↑ty-arr upB upB₁) (↑tyʲ-𝕚 upj)
  = s-arr₂ (sd-strengthen= s new upB upA ↑tyʲ-∞) (sd-strengthen= s₁ new upA₁ upB₁ upj)
sd-strengthen= (s-arr₃ regA s) new (↑ty-arr upA upA₁) (↑ty-arr upB upB₁) (↑tyʲ-𝕔 upj)
  with refl ← ↑ty-unique-inver upA upB
  = s-arr₃ (⊢r-strengthen= regA new upB) (sd-strengthen= s new upA₁ upB₁ upj)
sd-strengthen= (s-∀ s) new (↑ty-∀ upA) (↑ty-∀ upB) ↑tyʲ-∞
  = s-∀ (sd-strengthen= s (◀S∙ new) upA upB ↑tyʲ-∞)
sd-strengthen= {j = j} (s-∀l {B = B} grd regA' s ic fd upC upD upj₁) new (↑ty-∀ upA) (↑ty-arr {A = A′} {B = B′} upB upB₁) upj
  with ⟨ A″ , upA′ ⟩ ← ↑ty0-total A′
  with ⟨ B″ , upB′ ⟩ ← ↑ty0-total B′
  with ⟨ j' , upj' ⟩ ← ↑tyʲ0-total j
  with reg-S= regΓ regA ← s2-sregular s
  with k¬εB ← ⊢r-¬ε regA (◀=-∋=' new)
  with ⟨ preB , upB' ⟩ ← ↑ty-surjective k¬εB
  -- A%
  with regA% ← s2-⊢r-l s
  with k1¬εB ← ⊢r-¬ε regA% (S= (◀=-∋=' new))
  with ⟨ preA% , upA% ⟩ ← ↑ty-surjective k1¬εB
  = s-∀l (≫-strengthen= grd (reg-S= regΓ regA) (◀S= new upB') upA upA%)
         (⊢r-strengthen= regA' (◀S∙ new) upA)
         (sd-strengthen= s (◀S= new upB') upA% (↑ty-arr (↑ty-comm0' upB upC upA′) (↑ty-comm0' upB₁ upD upB′)) (↑tyʲ-comm0' upj upj₁ upj'))
         (𝕚𝕔-↑tyʲ' ic upj)
         (↑ty-find0' fd upA (↑tyʲ-comm0' upj upj₁ upj')) upA′ upB′ upj'
sd-strengthen= {j = j} (s-∀l-no-appear grd regA' s ic fd upC upD upj₁) new (↑ty-∀ upA) (↑ty-arr {A = A′} {B = B′} upB upB₁) upj
  with ⟨ A″ , upA′ ⟩ ← ↑ty0-total A′
  with ⟨ B″ , upB′ ⟩ ← ↑ty0-total B′
  with ⟨ j' , upj' ⟩ ← ↑tyʲ0-total j
  with reg-S^ regΓ  ← s2-sregular s
  -- A%
  with regA% ← s2-⊢r-l s
  with k1¬εB ← ⊢r-¬ε regA% (S^ (◀=-∋=' new))
  with ⟨ preA% , upA% ⟩ ← ↑ty-surjective k1¬εB
  = s-∀l-no-appear (≫-strengthen= grd (reg-S^ regΓ) (◀S^ new) upA upA%)
                   (⊢r-strengthen= regA' (◀S∙ new) upA)
                   (sd-strengthen= s (◀S^ new) upA% (↑ty-arr (↑ty-comm0' upB upC upA′) (↑ty-comm0' upB₁ upD upB′)) (↑tyʲ-comm0' upj upj₁ upj'))
                   (𝕚𝕔-↑tyʲ' ic upj)
                   (¬ε-↑ty'-inv0 fd upA)
                   upA′ upB′ upj'
sd-strengthen= (s-tapp grd regA' s upj₁) new (↑ty-∀ upA) (↑ty-∀ upB) (↑tyʲ-𝕥 {j = j} upj upA₁)
  with ⟨ j' , upj' ⟩ ← ↑tyʲ0-total j
  --
  with reg-S= regΓ regA ← s2-sregular s
  with k¬εB ← ⊢r-¬ε regA (◀=-∋=' new)
  with ⟨ preB , upB' ⟩ ← ↑ty-surjective k¬εB
  with regA% ← s2-⊢r-l s
  with k1¬εB ← ⊢r-¬ε regA% (S= (◀=-∋=' new))
  with ⟨ preA% , upA% ⟩ ← ↑ty-surjective k1¬εB
  = s-tapp (≫-strengthen= grd (reg-S= regΓ regA) (◀S= new upA₁) upA upA%)
           (⊢r-strengthen= regA' (◀S∙ new) upA)
           (sd-strengthen= s (◀S= new upA₁) upA% upB (↑tyʲ-comm0' upj upj₁ upj'))
           upj'


sd-strengthen=0 : Γ ,= T ⊢d² j' # A' ≤ B'
                  → ↑ty0 A ⇘ A'
                  → ↑ty0 B ⇘ B'
                  → ↑tyʲ0 j ⇘ j'
                  → Γ ⊢d² j # A ≤ B
sd-strengthen=0 s upA upB upj = sd-strengthen= s ◀Z upA upB upj


sd-refl-∞ : SRegular Γ
          → Γ ⊢r A
          → Γ ⊢d² ∞ # A ≤ A
sd-refl-∞ regΓ ⊢r-int = s-int regΓ
sd-refl-∞ regΓ (⊢r-var-∙ inΓ) = s-var-∙ regΓ inΓ
sd-refl-∞ regΓ (⊢r-arr regA regA₁) = s-arr₁ (sd-refl-∞ regΓ regA) (sd-refl-∞ regΓ regA₁)
sd-refl-∞ regΓ (⊢r-∀ regA) = s-∀ (sd-refl-∞ (reg-S∙ regΓ) regA)

sound : Γ ⊢ j # A ⌞ ≤ ⌝ B
      → Γ ≫ A ⇘ A%
      → Γ ≫ B ⇘ B%
      → Γ ⊢d² j # A% ≤ B%
sound (s-refl regΔ cloA grd) grd1 grd2
  with refl ← ≫-unique grd1 grd
  with refl ← ⊢r-≫-eq' (⊢c-≫-⊢r regΔ cloA grd1) grd2 = s-refl regΔ (⊢c-≫-⊢r regΔ cloA grd)
sound (s-int regΔ) grd-int grd-int = s-int regΔ
sound (s-var-∙ regΔ inΔ) (grd-var= x) (grd-var= x₁) = ⊥-elim (∋∙-∋:=-false inΔ x₁)
sound (s-var-∙ regΔ inΔ) (grd-var= x) (grd-var∙ x₁) = ⊥-elim (∋∙-∋:=-false inΔ x)
sound (s-var-∙ regΔ inΔ) (grd-var∙ x) (grd-var= x₁) = ⊥-elim (∋∙-∋:=-false inΔ x₁)
sound (s-var-∙ regΔ inΔ) (grd-var∙ x) (grd-var∙ x₁) = s-var-∙ regΔ x₁
sound (s-arr₁ s s₁) (grd-arr grd1 grd3) (grd-arr grd2 grd4) = s-arr₁ (sound s grd2 grd1) (sound s₁ grd3 grd4)
sound (s-arr₂ s s₁) (grd-arr grd1 grd3) (grd-arr grd2 grd4) = s-arr₂ (sound s grd2 grd1) (sound s₁ grd3 grd4)
sound (s-arr₃ cloA grd s) (grd-arr grd1 grd3) (grd-arr grd2 grd4)
  with refl ← ≫-unique grd grd1
  with regA ← ⊢c-≫-⊢r (I.s-sregular s) cloA grd
  with refl ← ⊢r-≫-eq' regA grd2 = s-arr₃ regA (sound s grd3 grd4)
sound (s-∀ s) (grd-∀ grd1) (grd-∀ grd2) = s-∀ (sound s grd1 grd2)
sound s'@(s-∀l {B = B} s ic fd upC upD upj) (grd-∀ grd1) grdCD@(grd-arr grd2 grd3)
  with cloA ← s-⊢c-l s
  with ⟨ A% , grdA ⟩ ← ≫-total (I.s-sregular s) cloA
  with reg-S= regΓ regA ← I.s-sregular s
  with regCD ← s+-polarity s'
  with refl ← ⊢r-≫-eq' regCD grdCD
  = s-∀l (≫-trans'' (reg-S∙ regΓ) grd1 (∙⟹^0 (proj₂ (↑ty0-total B)) regA) Z∙ grdA)
         (⊢c-≫-⊢r (reg-S∙ regΓ) (⊢c-◆0 (s-⊢c-l s)) grd1)
         (sound s grdA (⊢r-≫-eq (s+-polarity s)))
         ic
         (find-≫-∙' fd Z∙ Z grd1)
         upC
         upD
         upj
sound s'@(s-∀l-no-appear s ic fd upC upD upj) (grd-∀ grd1) grdCD@(grd-arr grd2 grd3)
  with cloA ← s-⊢c-l s
  with ⟨ A% , grdA ⟩ ← ≫-total (I.s-sregular s) cloA
  with reg-S^ regΓ ← I.s-sregular s
  with regCD ← s+-polarity s'
  with refl ← ⊢r-≫-eq' regCD grdCD
  with refl ← ≫-same grd1 ◈Z grdA fd
  = s-∀l-no-appear (⊢r-≫-eq (⊢c-≫-⊢r (reg-S^ regΓ) cloA grdA))
         (⊢c-≫-⊢r (reg-S∙ regΓ) (⊢c-◇0 (s-⊢c-l s)) grd1)
         (sound s grdA (⊢r-≫-eq (s+-polarity s)))
         ic
         (¬ε-≫-∙' fd Z Z∙ grd1)
         upC
         upD
         upj
sound (s-tapp {B = B} s upj) (grd-∀ grd1) (grd-∀ grd2)
  with cloA ← s-⊢c-l s
  with ⟨ A% , grdA ⟩ ← ≫-total (I.s-sregular s) cloA
  with reg-S= regΓ regA ← I.s-sregular s
  with refl ← ⊢r-≫-eq' (⊢r-◆0 (s+-polarity s)) grd2
  = s-tapp (≫-trans'' (reg-S∙ regΓ) grd1 (∙⟹^0 (proj₂ (↑ty0-total B)) regA) Z∙ grdA)
           (⊢c-≫-⊢r (reg-S∙ regΓ) (⊢c-◆0 cloA) grd1)
           (sound s grdA (⊢r-≫-eq (s+-polarity s))) upj
sound (s-svar-l x inΔ) (grd-var= x₁) grd2
  with refl ← ∋:=-unique inΔ x₁
  with regA ← ∋:=-⊢r x inΔ
  with refl ← ⊢r-≫-eq' regA grd2
  = sd-refl-∞ x regA
sound (s-svar-l x inΔ) (grd-var∙ x₁) grd2 = ⊥-elim (∋∙-∋:=-false x₁ inΔ)
sound (s-svar-r x inΔ) grd1 (grd-var= x₁)
  with refl ← ∋:=-unique inΔ x₁
  with regA ← ∋:=-⊢r x inΔ
  with refl ← ⊢r-≫-eq' regA grd1 = sd-refl-∞ x regA
sound (s-svar-r x inΔ) grd1 (grd-var∙ x₁) = ⊥-elim (∋∙-∋:=-false x₁ inΔ)
sound (s-svar-𝕚 inΓ s) (grd-var= x) (grd-arr grd2 grd3)
  with refl ← ∋:=-unique inΓ x = sound s (⊢r-≫-eq (∋:=-⊢r (I.s-sregular s) inΓ)) (grd-arr grd2 grd3)
sound (s-svar-𝕚 inΓ s) (grd-var∙ x) (grd-arr grd2 grd3) = ⊥-elim (∋∙-∋:=-false x inΓ)
sound (s-svar-𝕔 inΓ s) (grd-var= x) (grd-arr grd2 grd3)
  with refl ← ∋:=-unique inΓ x = sound s (⊢r-≫-eq (∋:=-⊢r (I.s-sregular s) inΓ)) (grd-arr grd2 grd3)
sound (s-svar-𝕔 inΓ s) (grd-var∙ x) grd2 = ⊥-elim (∋∙-∋:=-false x inΓ)
sound (s-svar-𝕥 inΓ s) (grd-var= x) (grd-∀ grd2)
  with refl ← ∋:=-unique inΓ x = sound s (⊢r-≫-eq (∋:=-⊢r (I.s-sregular s) inΓ)) (grd-∀ grd2)
sound (s-svar-𝕥 inΓ s) (grd-var∙ x) grd2 = ⊥-elim (∋∙-∋:=-false x inΓ)
