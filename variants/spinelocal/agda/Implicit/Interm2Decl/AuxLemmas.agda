module Implicit.Interm2Decl.AuxLemmas where

open import Implicit.Language.All
open import Implicit.Decl.All as D
open import Implicit.Interm.All as I


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
sd-strengthen= {j = j} (s-∀l-peek {B = B} grd regA' s ic fd upC upD upj₁) new (↑ty-∀ upA) (↑ty-arr {A = A′} {B = B′} upB upB₁) upj
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
  = s-∀l-peek (≫-strengthen= grd (reg-S= regΓ regA) (◀S= new upB') upA upA%)
         (⊢r-strengthen= regA' (◀S∙ new) upA)
         (sd-strengthen= s (◀S= new upB') upA% (↑ty-arr (↑ty-comm0' upB upC upA′) (↑ty-comm0' upB₁ upD upB′)) (↑tyʲ-comm0' upj upj₁ upj'))
         (𝕚𝕔-↑tyʲ' ic upj)
         (↑ty-peek0' fd upA (↑tyʲ-comm0' upj upj₁ upj')) upA′ upB′ upj'
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
