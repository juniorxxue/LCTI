module Implicit.Interm2Decl.AuxLemmas where

open import Implicit.Language.All
open import Implicit.Decl.All as D
open import Implicit.Interm.All as I


sd-strengthen= : Γ ⊢d² j # A' ≤ B'
               → Γ ◀ k =⇘ Γ'
               → A ↑ty k ⇘ A'
               → B ↑ty k ⇘ B'
               → Γ' ⊢d² j # A ≤ B
sd-strengthen= (s-refl regΔ cloA) new upA upB
  with refl ← ↑ty-unique-inver upA upB
  = s-refl (sregular-strengthen= regΔ new) (⊢r-strengthen= cloA new upB)
sd-strengthen= (s-int regΔ) new ↑ty-int ↑ty-int = s-int (sregular-strengthen= regΔ new)
sd-strengthen= {B = ‶ X} (s-var-∙ regΔ inΔ) new ↑ty-var upB
  with refl ← ↑ty-var-inv upB refl = s-var-∙ (sregular-strengthen= regΔ new) (∋∙-strengthen= inΔ new)
sd-strengthen= (s-arr₁ s s₁) new (↑ty-arr upA upA₁) (↑ty-arr upB upB₁)
  = s-arr₁ (sd-strengthen= s new upB upA) (sd-strengthen= s₁ new upA₁ upB₁)
sd-strengthen= (s-arr₂ s s₁) new (↑ty-arr upA upA₁) (↑ty-arr upB upB₁)
  = s-arr₂ (sd-strengthen= s new upB upA) (sd-strengthen= s₁ new upA₁ upB₁)
sd-strengthen= (s-arr₃ regA s) new (↑ty-arr upA upA₁) (↑ty-arr upB upB₁)
  with refl ← ↑ty-unique-inver upA upB
  = s-arr₃ (⊢r-strengthen= regA new upB) (sd-strengthen= s new upA₁ upB₁)
sd-strengthen= (s-∀ s) new (↑ty-∀ upA) (↑ty-∀ upB)
  = s-∀ (sd-strengthen= s (◀S∙ new) upA upB)
sd-strengthen= {j = j} (s-∀l {B = B} grd regA' s fd upC upD) new (↑ty-∀ upA) (↑ty-arr {A = A′} {B = B′} upB upB₁)
  with ⟨ A″ , upA′ ⟩ ← ↑ty0-total A′
  with ⟨ B″ , upB′ ⟩ ← ↑ty0-total B′
  with reg-S= regΓ regA ← s2-sregular s
  with k¬εB ← ⊢r-¬ε regA (◀=-∋=' new)
  with ⟨ preB , upB' ⟩ ← ↑ty-surjective k¬εB
  -- A%
  with regA% ← s2-⊢r-l s
  with k1¬εB ← ⊢r-¬ε regA% (S= (◀=-∋=' new))
  with ⟨ preA% , upA% ⟩ ← ↑ty-surjective k1¬εB
  = s-∀l (≫-strengthen= grd (reg-S= regΓ regA) (◀S= new upB') upA upA%)
         (⊢r-strengthen= regA' (◀S∙ new) upA)
         (sd-strengthen= s (◀S= new upB') upA% (↑ty-arr (↑ty-comm0' upB upC upA′) (↑ty-comm0' upB₁ upD upB′)))
         (↑ty-find0' fd upA) upA′ upB′
sd-strengthen= {j = j} (s-∀l-no-appear grd regA' s fd upC upD) new (↑ty-∀ upA) (↑ty-arr {A = A′} {B = B′} upB upB₁)
  with ⟨ A″ , upA′ ⟩ ← ↑ty0-total A′
  with ⟨ B″ , upB′ ⟩ ← ↑ty0-total B′
  with reg-S^ regΓ  ← s2-sregular s
  -- A%
  with regA% ← s2-⊢r-l s
  with k1¬εB ← ⊢r-¬ε regA% (S^ (◀=-∋=' new))
  with ⟨ preA% , upA% ⟩ ← ↑ty-surjective k1¬εB
  = s-∀l-no-appear (≫-strengthen= grd (reg-S^ regΓ) (◀S^ new) upA upA%)
                   (⊢r-strengthen= regA' (◀S∙ new) upA)
                   (sd-strengthen= s (◀S^ new) upA% (↑ty-arr (↑ty-comm0' upB upC upA′) (↑ty-comm0' upB₁ upD upB′)))
                   (¬ε-↑ty'-inv0 fd upA)
                   upA′ upB′


sd-strengthen=0 : Γ ,= T ⊢d² j # A' ≤ B'
                  → ↑ty0 A ⇘ A'
                  → ↑ty0 B ⇘ B'
                  → Γ ⊢d² j # A ≤ B
sd-strengthen=0 s upA upB = sd-strengthen= s ◀Z upA upB


sd-refl-∞ : SRegular Γ
          → Γ ⊢r A
          → Γ ⊢d² `□ # A ≤ A
sd-refl-∞ regΓ ⊢r-int = s-int regΓ
sd-refl-∞ regΓ (⊢r-var-∙ inΓ) = s-var-∙ regΓ inΓ
sd-refl-∞ regΓ (⊢r-arr regA regA₁) = s-arr₁ (sd-refl-∞ regΓ regA) (sd-refl-∞ regΓ regA₁)
sd-refl-∞ regΓ (⊢r-∀ regA) = s-∀ (sd-refl-∞ (reg-S∙ regΓ) regA)
