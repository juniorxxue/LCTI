module Implicit.Interm.Properties.Strengthen2 where

open import Implicit.Language.All
open import Implicit.Interm.Base
open import Implicit.Interm.Properties.Regularity
open import Implicit.Interm.Properties.Polarity


s-strengthen^ : Γ ⊢ j' # A' ⌞ ≤ ⌝ B'
              → Γ ◀ k ^⇘ Γ'
              → A ↑ty k ⇘ A'
              → B ↑ty k ⇘ B'
              → j ↑tyʲ k ⇘ j'
              → Γ' ⊢ j # A ⌞ ≤ ⌝ B
s-strengthen^ (s-refl regΔ cloA grd) newΓ upA upB ↑tyʲ-Z = s-refl (sregular-strengthen^ regΔ newΓ)
                                                           (⊢c-strengthen^ cloA newΓ upA)
                                                           (≫-strengthen^ grd regΔ newΓ upA upB)
s-strengthen^ (s-int regΔ) newΓ ↑ty-int ↑ty-int ↑tyʲ-∞ = s-int (sregular-strengthen^ regΔ newΓ)
s-strengthen^ (s-top+ regΔ regA) newΓ upA ↑ty-top ↑tyʲ-∞ = s-top+ (sregular-strengthen^ regΔ newΓ) (⊢c-strengthen^ regA newΓ upA)
s-strengthen^ (s-top- regΔ regA) newΓ upA ↑ty-top ↑tyʲ-∞ = s-top- (sregular-strengthen^ regΔ newΓ) (⊢r-strengthen^ regA newΓ upA)
s-strengthen^ (s-bot+ regΔ regA regj) newΓ ↑ty-bot upA upj = s-bot+ (sregular-strengthen^ regΔ newΓ) (⊢r-strengthen^ regA newΓ upA) {!!}
s-strengthen^ (s-bot- regΔ regA) newΓ ↑ty-bot upA ↑tyʲ-∞ = s-bot- (sregular-strengthen^ regΔ newΓ) (⊢c-strengthen^ regA newΓ upA)
s-strengthen^ {B = ‶ X} (s-var-∙ regΔ inΔ) newΓ ↑ty-var upB ↑tyʲ-∞
  with refl ← ↑ty-var-inv upB refl = s-var-∙ (sregular-strengthen^ regΔ newΓ) (∋∙-strengthen^ inΔ newΓ)
s-strengthen^ (s-arr₁ s s₁) newΓ (↑ty-arr upA upA₁) (↑ty-arr upB upB₁) ↑tyʲ-∞
  = s-arr₁ (s-strengthen^ s newΓ upB upA ↑tyʲ-∞) (s-strengthen^ s₁ newΓ upA₁ upB₁ ↑tyʲ-∞)
s-strengthen^ (s-arr₂ s s₁) newΓ (↑ty-arr upA upA₁) (↑ty-arr upB upB₁) (↑tyʲ-𝕚 upj)
  = s-arr₂ (s-strengthen^ s newΓ upB upA ↑tyʲ-∞) (s-strengthen^ s₁ newΓ upA₁ upB₁ upj)
s-strengthen^ (s-arr₃ cloA grd s) newΓ (↑ty-arr upA upA₁) (↑ty-arr upB upB₁) (↑tyʲ-𝕔 upj)
  = s-arr₃ (⊢c-strengthen^ cloA newΓ upA) (≫-strengthen^ grd (s-sregular s) newΓ upA upB) (s-strengthen^ s newΓ upA₁ upB₁ upj)
s-strengthen^ (s-∀ s) newΓ (↑ty-∀ upA) (↑ty-∀ upB) ↑tyʲ-∞ = s-∀ (s-strengthen^ s (◀S∙ newΓ) upA upB ↑tyʲ-∞)
s-strengthen^ {j = j} (s-∀l {B = B} s ic fd upC upD upj₁) newΓ (↑ty-∀ upA) (↑ty-arr {A = A′} {B = B′} upB upB₁) upj
  with ⟨ A″ , upA′ ⟩ ← ↑ty0-total A′
  with ⟨ B″ , upB′ ⟩ ← ↑ty0-total B′
  with ⟨ j' , upj' ⟩ ← ↑tyʲ0-total j
  with reg-S= regΓ regA ← s-sregular s
  with k¬εB ← ⊢r-¬ε-^ regA (◀^-∋^' newΓ)
  with ⟨ preB , upB' ⟩ ← ↑ty-surjective k¬εB
    = s-∀l (s-strengthen^ s (◀S= newΓ upB') upA (↑ty-arr (↑ty-comm0' upB upC upA′) (↑ty-comm0' upB₁ upD upB′)) (↑tyʲ-comm0' upj upj₁ upj'))
           (𝕚𝕔-↑tyʲ' ic upj) (↑ty-find0' fd upA (↑tyʲ-comm0' upj upj₁ upj')) upA′ upB′ upj'
s-strengthen^ {j = j} (s-∀l-no-appear s ic fd upC upD upj₁) newΓ (↑ty-∀ upA) (↑ty-arr {A = A′} {B = B′} upB upB₁) upj
  with ⟨ A″ , upA′ ⟩ ← ↑ty0-total A′
  with ⟨ B″ , upB′ ⟩ ← ↑ty0-total B′
  with ⟨ j' , upj' ⟩ ← ↑tyʲ0-total j
  with reg-S^ regΓ ← s-sregular s
    = s-∀l-no-appear (s-strengthen^ s (◀S^ newΓ) upA (↑ty-arr (↑ty-comm0' upB upC upA′) (↑ty-comm0' upB₁ upD upB′)) (↑tyʲ-comm0' upj upj₁ upj'))
           (𝕚𝕔-↑tyʲ' ic upj) (¬ε-↑ty'-inv fd upA (s≤s z≤n)) upA′ upB′ upj'
s-strengthen^ (s-tapp s upj₁) newΓ (↑ty-∀ upA) (↑ty-∀ upB) (↑tyʲ-𝕥 {j = j} upj upA₁)
  with ⟨ j' , upj' ⟩ ← ↑tyʲ0-total j
  = s-tapp (s-strengthen^ s (◀S= newΓ upA₁) upA upB (↑tyʲ-comm0' upj upj₁ upj')) upj'
s-strengthen^ (s-svar-l x inΔ) newΓ ↑ty-var upB upj = {!!}
s-strengthen^ (s-svar-r x inΔ) newΓ upA ↑ty-var ↑tyʲ-∞ = {!!}


t-strengthen^ : Γ ⊢ j' # e' ⦂ A'
                → Γ ◀ k ^⇘ Γ'
                → e ↑tyᵉ k ⇘ e'
                → A ↑ty k ⇘ A'
                → j ↑tyʲ k ⇘ j'
                → Γ' ⊢ j # e ⦂ A
t-strengthen^ (⊢lit regΓ) newΓ ↑tyᵉ-lit ↑ty-int ↑tyʲ-Z = ⊢lit (tregular-strengthen^ regΓ newΓ)
t-strengthen^ (⊢var regΓ x∈Γ) newΓ ↑tyᵉ-var upA ↑tyʲ-Z = ⊢var (tregular-strengthen^ regΓ newΓ)
                                                              (∋⦂-strengthen^ x∈Γ regΓ newΓ upA)
t-strengthen^ (⊢ann ⊢e) newΓ (↑tyᵉ-⦂ upe up) upA ↑tyʲ-Z
  with refl ← ↑ty-unique-inver up upA = ⊢ann (t-strengthen^ ⊢e newΓ upe up ↑tyʲ-∞)
t-strengthen^ (⊢lam₁ ⊢e) newΓ (↑tyᵉ-ƛ upe) (↑ty-arr upA upA₁) ↑tyʲ-∞ = ⊢lam₁ (t-strengthen^ ⊢e (◀S, newΓ upA) upe upA₁ ↑tyʲ-∞)
t-strengthen^ (⊢lam₂ ⊢e) newΓ (↑tyᵉ-ƛ upe) (↑ty-arr upA upA₁) (↑tyʲ-𝕚 upj) = ⊢lam₂ (t-strengthen^ ⊢e (◀S, newΓ upA) upe upA₁ upj)
t-strengthen^ (⊢app₁ ⊢e ⊢e₁) newΓ (↑tyᵉ-app upe upe₁) upA upj
  with ⊢r-arr r r₁ ← t-⊢r ⊢e
  with ⟨ preA , upp ⟩ ← ⊢r-◀^-↑ty-surjective r newΓ = ⊢app₁ (t-strengthen^ ⊢e newΓ upe (↑ty-arr upp upA) (↑tyʲ-𝕔 upj))
                                                           (t-strengthen^ ⊢e₁ newΓ upe₁ upp ↑tyʲ-∞)
t-strengthen^ (⊢app₂ ⊢e ⊢e₁) newΓ (↑tyᵉ-app upe upe₁) upA upj
  with ⊢r-arr r r₁ ← t-⊢r ⊢e
  with ⟨ preA , upp ⟩ ← ⊢r-◀^-↑ty-surjective r newΓ = ⊢app₂ (t-strengthen^ ⊢e newΓ upe (↑ty-arr upp upA) (↑tyʲ-𝕚 upj))
                                                           (t-strengthen^ ⊢e₁ newΓ upe₁ upp ↑tyʲ-Z)
t-strengthen^ (⊢sub ⊢e B≤A gc j≢Z) newΓ upe upA upj
  with r ← t-⊢r ⊢e
  with ⟨ preA , upp ⟩ ← ⊢r-◀^-↑ty-surjective r newΓ = ⊢sub (t-strengthen^ ⊢e newΓ upe upp ↑tyʲ-Z) (s-strengthen^ B≤A (◀S⋈ newΓ) upp upA upj)
                                                          (↑ty-gc' gc upe) (nonz-↑tyʲ' j≢Z upj)
t-strengthen^ (⊢tabs ⊢e) newΓ (↑tyᵉ-Λ upe) (↑ty-∀ upA) ↑tyʲ-Z = ⊢tabs (t-strengthen^ ⊢e (◀S∙ newΓ) upe upA ↑tyʲ-Z)
t-strengthen^ (⊢tapp ⊢e st) newΓ (↑tyᵉ-⓪ upe upA₁) upA upj
  with r ← t-⊢r ⊢e
  with ⟨ preA , ↑ty-∀ upp ⟩ ← ⊢r-◀^-↑ty-surjective r newΓ
  = ⊢tapp (t-strengthen^ ⊢e newΓ upe (↑ty-∀ upp) (↑tyʲ-𝕥 upj upA₁)) (↑ty-st-comm0'' st upA₁ upp upA)
