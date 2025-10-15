module Implicit.Interm.Properties.Strengthen where

open import Implicit.Language.All
open import Implicit.Interm.Base
open import Implicit.Interm.Properties.Regularity
open import Implicit.Interm.Properties.Polarity

s-strengthen, : Γ ⊢ j # A ⌞ ≤ ⌝ B
              → Γ ◀ k ,⇘ Γ'
              → Γ' ⊢ j # A ⌞ ≤ ⌝ B
s-strengthen, (s-refl regΔ cloA grd) newΓ = s-refl (sregular-strengthen, regΔ newΓ) (⊢c-strengthen, cloA newΓ) (≫-strengthen, grd newΓ)
s-strengthen, (s-int regΔ) newΓ = s-int (sregular-strengthen, regΔ newΓ)
s-strengthen, (s-var-∙ regΔ inΔ) newΓ = s-var-∙ (sregular-strengthen, regΔ newΓ) (∋∙-strengthen, inΔ newΓ)
s-strengthen, (s-arr₁ s s₁) newΓ = s-arr₁ (s-strengthen, s newΓ) (s-strengthen, s₁ newΓ)
s-strengthen, (s-arr₂ s s₁) newΓ = s-arr₂ (s-strengthen, s newΓ) (s-strengthen, s₁ newΓ)
s-strengthen, (s-arr₃ cloA grd s) newΓ = s-arr₃ (⊢c-strengthen, cloA newΓ) (≫-strengthen, grd newΓ) (s-strengthen, s newΓ)
s-strengthen, (s-∀ s) newΓ = s-∀ (s-strengthen, s (◀S∙ newΓ))
s-strengthen, (s-∀l s fd upC upD) newΓ = s-∀l (s-strengthen, s (◀S= newΓ)) fd upC upD
s-strengthen, (s-∀l-no-appear s fd upC upD) newΓ = s-∀l-no-appear (s-strengthen, s (◀S^ newΓ)) fd upC upD
s-strengthen, (s-svar-l inΔ s) newΓ = s-svar-l (∋:=-strengthen, inΔ newΓ) (s-strengthen, s newΓ)
s-strengthen, (s-svar-r x inΔ) newΓ = s-svar-r (sregular-strengthen, x newΓ) (∋:=-strengthen, inΔ newΓ)


t-strengthen, : Γ ⊢ j # e' ⦂ A
              → Γ ◀ k ,⇘ Γ'
              → e ↑tm k ⇘ e'
              → Γ' ⊢ j # e ⦂ A
t-strengthen, (⊢lit cloΓ) newΓ ↑tm-lit = ⊢lit (tregular-strengthen, cloΓ newΓ)
t-strengthen, (⊢var cloΓ x∈Γ) newΓ ↑tm-var = ⊢var (tregular-strengthen, cloΓ newΓ) (∋⦂-strengthen, x∈Γ newΓ)
t-strengthen, (⊢ann ⊢e) newΓ (↑tm-⦂ upe) = ⊢ann (t-strengthen, ⊢e newΓ upe)
t-strengthen, (⊢lam₁ ⊢e) newΓ (↑tm-ƛ upe) = ⊢lam₁ (t-strengthen, ⊢e (◀S, newΓ) upe)
t-strengthen, (⊢lam₂ ⊢e) newΓ (↑tm-ƛ upe) = ⊢lam₂ (t-strengthen, ⊢e (◀S, newΓ) upe)
t-strengthen, (⊢app ⊢e ⊢e₁) newΓ (↑tm-app upe upe₁) = ⊢app (t-strengthen, ⊢e newΓ upe) (t-strengthen, ⊢e₁ newΓ upe₁)
t-strengthen, (⊢sub ⊢e B≤A gc j≢Z) newΓ upe = ⊢sub (t-strengthen, ⊢e newΓ upe) (s-strengthen, B≤A (◀S⋈ newΓ)) (↑tm-gc' gc upe) j≢Z
t-strengthen, (⊢tabs ⊢e) newΓ (↑tm-Λ upe) = ⊢tabs (t-strengthen, ⊢e (◀S∙ newΓ) upe)
t-strengthen, (⊢tapp ⊢e regA st s) newΓ (↑tm-⓪ upe)
  = ⊢tapp (t-strengthen, ⊢e newΓ upe) (⊢r-strengthen, regA newΓ) st (s-strengthen, s (◀S⋈ newΓ))

t-strengthen,0 : Γ , T ⊢ j # e' ⦂ A
               → ↑tm0 e ⇘ e'
               → Γ ⊢ j # e ⦂ A
t-strengthen,0 ⊢e up = t-strengthen, ⊢e ◀Z up


-- sometimes, we need a shifted over environments, k εᵍ Γ
s-strengthen= : Γ ⊢ j # A' ⌞ ≤ ⌝ B'
              → Γ ◀ k =⇘ Γ'
              → A ↑ty k ⇘ A'
              → B ↑ty k ⇘ B'
              → Γ' ⊢ j # A ⌞ ≤ ⌝ B
s-strengthen= (s-refl regΔ cloA grd) newΓ upA upB = s-refl (sregular-strengthen= regΔ newΓ)
                                                           (⊢c-strengthen= cloA newΓ upA)
                                                           (≫-strengthen= grd regΔ newΓ upA upB)
s-strengthen= (s-int regΔ) newΓ ↑ty-int ↑ty-int = s-int (sregular-strengthen= regΔ newΓ)
s-strengthen= {B = ‶ X} (s-var-∙ regΔ inΔ) newΓ ↑ty-var upB
  with refl ← ↑ty-var-inv upB refl = s-var-∙ (sregular-strengthen= regΔ newΓ) (∋∙-strengthen= inΔ newΓ)
s-strengthen= (s-arr₁ s s₁) newΓ (↑ty-arr upA upA₁) (↑ty-arr upB upB₁)
  = s-arr₁ (s-strengthen= s newΓ upB upA) (s-strengthen= s₁ newΓ upA₁ upB₁)
s-strengthen= (s-arr₂ s s₁) newΓ (↑ty-arr upA upA₁) (↑ty-arr upB upB₁)
  = s-arr₂ (s-strengthen= s newΓ upB upA) (s-strengthen= s₁ newΓ upA₁ upB₁)
s-strengthen= (s-arr₃ cloA grd s) newΓ (↑ty-arr upA upA₁) (↑ty-arr upB upB₁)
  = s-arr₃ (⊢c-strengthen= cloA newΓ upA) (≫-strengthen= grd (s-sregular s) newΓ upA upB) (s-strengthen= s newΓ upA₁ upB₁)
s-strengthen= (s-∀ s) newΓ (↑ty-∀ upA) (↑ty-∀ upB) = s-∀ (s-strengthen= s (◀S∙ newΓ) upA upB)
s-strengthen= {j = j} (s-∀l {B = B} s fd upC upD) newΓ (↑ty-∀ upA) (↑ty-arr {A = A′} {B = B′} upB upB₁)
  with ⟨ A″ , upA′ ⟩ ← ↑ty0-total A′
  with ⟨ B″ , upB′ ⟩ ← ↑ty0-total B′
  with reg-S= regΓ regA ← s-sregular s
  with k¬εB ← ⊢r-¬ε regA (◀=-∋=' newΓ)
  with ⟨ preB , upB' ⟩ ← ↑ty-surjective k¬εB
    = s-∀l (s-strengthen= s (◀S= newΓ upB') upA (↑ty-arr (↑ty-comm0' upB upC upA′) (↑ty-comm0' upB₁ upD upB′)))
           (↑ty-find0' fd upA) upA′ upB′
s-strengthen= {j = j} (s-∀l-no-appear s fd upC upD) newΓ (↑ty-∀ upA) (↑ty-arr {A = A′} {B = B′} upB upB₁)
  with ⟨ A″ , upA′ ⟩ ← ↑ty0-total A′
  with ⟨ B″ , upB′ ⟩ ← ↑ty0-total B′
  with reg-S^ regΓ ← s-sregular s
    = s-∀l-no-appear (s-strengthen= s (◀S^ newΓ) upA (↑ty-arr (↑ty-comm0' upB upC upA′) (↑ty-comm0' upB₁ upD upB′)))
           (¬ε-↑ty'-inv fd upA (s≤s z≤n)) upA′ upB′
s-strengthen= (s-svar-l {B = B′} inΔ s) newΓ ↑ty-var upB
  with regA ← ∋:=-⊢r (s-sregular s) inΔ
  with k¬εB ← ⊢r-¬ε regA (◀=-∋=' newΓ)
  with ⟨ preB , upB' ⟩ ← ↑ty-surjective k¬εB
  = s-svar-l (∋:=-strengthen=-reg (s-sregular s) inΔ newΓ upB') (s-strengthen= s newΓ upB' upB)
s-strengthen= (s-svar-r x inΔ) newΓ upA ↑ty-var = s-svar-r (sregular-strengthen= x newΓ) (∋:=-strengthen=-reg x inΔ newΓ upA)

t-strengthen= : Γ ⊢ j # e' ⦂ A'
                → Γ ◀ k =⇘ Γ'
                → e ↑tyᵉ k ⇘ e'
                → A ↑ty k ⇘ A'
                → Γ' ⊢ j # e ⦂ A
t-strengthen= (⊢lit regΓ) newΓ ↑tyᵉ-lit ↑ty-int = ⊢lit (tregular-strengthen= regΓ newΓ)
t-strengthen= (⊢var regΓ x∈Γ) newΓ ↑tyᵉ-var upA = ⊢var (tregular-strengthen= regΓ newΓ)
                                                              (∋⦂-strengthen= x∈Γ regΓ newΓ upA)
t-strengthen= (⊢ann ⊢e) newΓ (↑tyᵉ-⦂ upe up) upA
  with refl ← ↑ty-unique-inver up upA = ⊢ann (t-strengthen= ⊢e newΓ upe up)
t-strengthen= (⊢lam₁ ⊢e) newΓ (↑tyᵉ-ƛ upe) (↑ty-arr upA upA₁) = ⊢lam₁ (t-strengthen= ⊢e (◀S, newΓ upA) upe upA₁)
t-strengthen= (⊢lam₂ ⊢e) newΓ (↑tyᵉ-ƛ upe) (↑ty-arr upA upA₁) = ⊢lam₂ (t-strengthen= ⊢e (◀S, newΓ upA) upe upA₁)
t-strengthen= (⊢app ⊢e ⊢e₁) newΓ (↑tyᵉ-app upe upe₁) upA
  with ⊢r-arr r r₁ ← t-⊢r ⊢e
  with ⟨ preA , upp ⟩ ← ⊢r-◀=-↑ty-surjective r newΓ = ⊢app (t-strengthen= ⊢e newΓ upe (↑ty-arr upp upA))
                                                           (t-strengthen= ⊢e₁ newΓ upe₁ upp)
t-strengthen= (⊢sub ⊢e B≤A gc j≢Z) newΓ upe upA
  with r ← t-⊢r ⊢e
  with ⟨ preA , upp ⟩ ← ⊢r-◀=-↑ty-surjective r newΓ = ⊢sub (t-strengthen= ⊢e newΓ upe upp) (s-strengthen= B≤A (◀S⋈ newΓ) upp upA)
                                                           (↑ty-gc' gc upe) j≢Z
t-strengthen= (⊢tabs ⊢e) newΓ (↑tyᵉ-Λ upe) (↑ty-∀ upA) = ⊢tabs (t-strengthen= ⊢e (◀S∙ newΓ) upe upA)
t-strengthen= (⊢tapp ⊢e regA st s) newΓ (↑tyᵉ-⓪ upe upA₁) upA
  with ⟨ preA , upp ⟩ ← ⊢r-◀=-↑ty-surjective (st0-⊢r (t-⊢r ⊢e) regA st) newΓ
  with ⊢r-∀ regB ← (t-⊢r ⊢e)
  with ⟨ preB , upp' ⟩ ← ⊢r-◀=-↑ty-surjective regB (◀S∙ newΓ)
  = ⊢tapp (t-strengthen= ⊢e newΓ upe (↑ty-∀ upp'))
          (⊢r-strengthen= regA newΓ upA₁) (↑ty-st-comm0'' st upA₁ upp' upp) (s-strengthen= s (◀S⋈ newΓ) upp upA)

s-strengthen^ : Γ ⊢ j # A' ⌞ ≤ ⌝ B'
              → Γ ◀ k ^⇘ Γ'
              → A ↑ty k ⇘ A'
              → B ↑ty k ⇘ B'
              → Γ' ⊢ j # A ⌞ ≤ ⌝ B
s-strengthen^ (s-refl regΔ cloA grd) newΓ upA upB = s-refl (sregular-strengthen^ regΔ newΓ)
                                                           (⊢c-strengthen^ cloA newΓ upA)
                                                           (≫-strengthen^ grd regΔ newΓ upA upB)
s-strengthen^ (s-int regΔ) newΓ ↑ty-int ↑ty-int = s-int (sregular-strengthen^ regΔ newΓ)
s-strengthen^ {B = ‶ X} (s-var-∙ regΔ inΔ) newΓ ↑ty-var upB
  with refl ← ↑ty-var-inv upB refl = s-var-∙ (sregular-strengthen^ regΔ newΓ) (∋∙-strengthen^ inΔ newΓ)
s-strengthen^ (s-arr₁ s s₁) newΓ (↑ty-arr upA upA₁) (↑ty-arr upB upB₁)
  = s-arr₁ (s-strengthen^ s newΓ upB upA) (s-strengthen^ s₁ newΓ upA₁ upB₁)
s-strengthen^ (s-arr₂ s s₁) newΓ (↑ty-arr upA upA₁) (↑ty-arr upB upB₁)
  = s-arr₂ (s-strengthen^ s newΓ upB upA) (s-strengthen^ s₁ newΓ upA₁ upB₁)
s-strengthen^ (s-arr₃ cloA grd s) newΓ (↑ty-arr upA upA₁) (↑ty-arr upB upB₁)
  = s-arr₃ (⊢c-strengthen^ cloA newΓ upA) (≫-strengthen^ grd (s-sregular s) newΓ upA upB) (s-strengthen^ s newΓ upA₁ upB₁)
s-strengthen^ (s-∀ s) newΓ (↑ty-∀ upA) (↑ty-∀ upB)  = s-∀ (s-strengthen^ s (◀S∙ newΓ) upA upB)
s-strengthen^ {j = j} (s-∀l {B = B} s fd upC upD) newΓ (↑ty-∀ upA) (↑ty-arr {A = A′} {B = B′} upB upB₁)
  with ⟨ A″ , upA′ ⟩ ← ↑ty0-total A′
  with ⟨ B″ , upB′ ⟩ ← ↑ty0-total B′
  with reg-S= regΓ regA ← s-sregular s
  with k¬εB ← ⊢r-¬ε-^ regA (◀^-∋^' newΓ)
  with ⟨ preB , upB' ⟩ ← ↑ty-surjective k¬εB
    = s-∀l (s-strengthen^ s (◀S= newΓ upB') upA (↑ty-arr (↑ty-comm0' upB upC upA′) (↑ty-comm0' upB₁ upD upB′)))
           (↑ty-find0' fd upA) upA′ upB′
s-strengthen^ {j = j} (s-∀l-no-appear s fd upC upD) newΓ (↑ty-∀ upA) (↑ty-arr {A = A′} {B = B′} upB upB₁)
  with ⟨ A″ , upA′ ⟩ ← ↑ty0-total A′
  with ⟨ B″ , upB′ ⟩ ← ↑ty0-total B′
  with reg-S^ regΓ ← s-sregular s
    = s-∀l-no-appear (s-strengthen^ s (◀S^ newΓ) upA (↑ty-arr (↑ty-comm0' upB upC upA′) (↑ty-comm0' upB₁ upD upB′)))
           (¬ε-↑ty'-inv fd upA (s≤s z≤n)) upA′ upB′
s-strengthen^ (s-svar-l inΔ s) newΓ ↑ty-var upB
  with regA ← ∋:=-⊢r (s-sregular s) inΔ
  with k¬εB ← ⊢r-¬ε-^ regA (◀^-∋^' newΓ)
  with ⟨ preB , upB' ⟩ ← ↑ty-surjective k¬εB
  = s-svar-l (∋:=-strengthen^-reg (s-sregular s) inΔ newΓ upB') (s-strengthen^ s newΓ upB' upB)
s-strengthen^ (s-svar-r x inΔ) newΓ upA ↑ty-var = s-svar-r (sregular-strengthen^ x newΓ) (∋:=-strengthen^-reg x inΔ newΓ upA)

t-strengthen^ : Γ ⊢ j # e' ⦂ A'
                → Γ ◀ k ^⇘ Γ'
                → e ↑tyᵉ k ⇘ e'
                → A ↑ty k ⇘ A'
                → Γ' ⊢ j # e ⦂ A
t-strengthen^ (⊢lit regΓ) newΓ ↑tyᵉ-lit ↑ty-int = ⊢lit (tregular-strengthen^ regΓ newΓ)
t-strengthen^ (⊢var regΓ x∈Γ) newΓ ↑tyᵉ-var upA = ⊢var (tregular-strengthen^ regΓ newΓ)
                                                              (∋⦂-strengthen^ x∈Γ regΓ newΓ upA)
t-strengthen^ (⊢ann ⊢e) newΓ (↑tyᵉ-⦂ upe up) upA
  with refl ← ↑ty-unique-inver up upA = ⊢ann (t-strengthen^ ⊢e newΓ upe up)
t-strengthen^ (⊢lam₁ ⊢e) newΓ (↑tyᵉ-ƛ upe) (↑ty-arr upA upA₁) = ⊢lam₁ (t-strengthen^ ⊢e (◀S, newΓ upA) upe upA₁)
t-strengthen^ (⊢lam₂ ⊢e) newΓ (↑tyᵉ-ƛ upe) (↑ty-arr upA upA₁) = ⊢lam₂ (t-strengthen^ ⊢e (◀S, newΓ upA) upe upA₁)
t-strengthen^ (⊢app ⊢e ⊢e₁) newΓ (↑tyᵉ-app upe upe₁) upA
  with ⊢r-arr r r₁ ← t-⊢r ⊢e
  with ⟨ preA , upp ⟩ ← ⊢r-◀^-↑ty-surjective r newΓ = ⊢app (t-strengthen^ ⊢e newΓ upe (↑ty-arr upp upA))
                                                           (t-strengthen^ ⊢e₁ newΓ upe₁ upp)
t-strengthen^ (⊢sub ⊢e B≤A gc j≢Z) newΓ upe upA
  with r ← t-⊢r ⊢e
  with ⟨ preA , upp ⟩ ← ⊢r-◀^-↑ty-surjective r newΓ = ⊢sub (t-strengthen^ ⊢e newΓ upe upp) (s-strengthen^ B≤A (◀S⋈ newΓ) upp upA)
                                                          (↑ty-gc' gc upe) j≢Z
t-strengthen^ (⊢tabs ⊢e) newΓ (↑tyᵉ-Λ upe) (↑ty-∀ upA) = ⊢tabs (t-strengthen^ ⊢e (◀S∙ newΓ) upe upA)
t-strengthen^ (⊢tapp ⊢e regA st s) newΓ (↑tyᵉ-⓪ upe upA₁) upA
  with ⟨ preA , upp ⟩ ← ⊢r-◀^-↑ty-surjective (st0-⊢r (t-⊢r ⊢e) regA st) newΓ
  with ⊢r-∀ regB ← (t-⊢r ⊢e)
  with ⟨ preB , upp' ⟩ ← ⊢r-◀^-↑ty-surjective regB (◀S∙ newΓ)
  = ⊢tapp (t-strengthen^ ⊢e newΓ upe (↑ty-∀ upp')) (⊢r-strengthen^ regA newΓ upA₁) (↑ty-st-comm0'' st upA₁ upp' upp)
          (s-strengthen^ s (◀S⋈ newΓ) upp upA)
