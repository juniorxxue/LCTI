module Implicit.Interm.Properties.Strengthen where

open import Implicit.Language.All
open import Implicit.Interm.Base
open import Implicit.Interm.Properties.Regularity
open import Implicit.Interm.Properties.Find

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
s-strengthen, (s-∀l s ic fd upC upD) newΓ = s-∀l (s-strengthen, s (◀S= newΓ)) ic fd upC upD
s-strengthen, (s-svar-l x inΔ) newΓ = s-svar-l (sregular-strengthen, x newΓ) (∋:=-strengthen, inΔ newΓ)
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
t-strengthen, (⊢app₁ ⊢e ⊢e₁) newΓ (↑tm-app upe upe₁) = ⊢app₁ (t-strengthen, ⊢e newΓ upe) (t-strengthen, ⊢e₁ newΓ upe₁)
t-strengthen, (⊢app₂ ⊢e ⊢e₁) newΓ (↑tm-app upe upe₁) = ⊢app₂ (t-strengthen, ⊢e newΓ upe) (t-strengthen, ⊢e₁ newΓ upe₁)
t-strengthen, (⊢sub ⊢e B≤A gc j≢Z) newΓ upe = ⊢sub (t-strengthen, ⊢e newΓ upe) (s-strengthen, B≤A (◀S⋈ newΓ)) (↑tm-gc' gc upe) j≢Z
t-strengthen, (⊢tabs ⊢e) newΓ (↑tm-Λ upe) = ⊢tabs (t-strengthen, ⊢e (◀S∙ newΓ) upe)

t-strengthen,0 : Γ , T ⊢ j # e' ⦂ A
               → ↑tm0 e ⇘ e'
               → Γ ⊢ j # e ⦂ A
t-strengthen,0 ⊢e up = t-strengthen, ⊢e ◀Z up

sregular-strengthen= : SRegular Γ
                     → Γ ◀ k =⇘ Γ'
                     → SRegular Γ'

⊢c-strengthen= : Γ ⊢c A'
               → Γ ◀ k =⇘ Γ'
               → A ↑ty k ⇘ A'
               → Γ' ⊢c A

≫-strengthen= : Γ ≫ A' ⇘ B'
              → Γ ◀ k =⇘ Γ'
              → A ↑ty k ⇘ A'
              → B ↑ty k ⇘ B'
              → Γ' ≫ A ⇘ B


∋∙-∋='-≢ : Γ ∋=' k
         → Γ ∋∙ X
         → X ≢ k
∋∙-∋='-≢ Z (S= inΓ2) = λ ()
∋∙-∋='-≢ (S∙ inΓ1) Z = λ ()
∋∙-∋='-≢ (S∙ inΓ1) (S∙ inΓ2) = ≢-suc (∋∙-∋='-≢ inΓ1 inΓ2)
∋∙-∋='-≢ (S^ inΓ1) (S^ inΓ2) = ≢-suc (∋∙-∋='-≢ inΓ1 inΓ2)
∋∙-∋='-≢ (S= inΓ1) (S= inΓ2) = ≢-suc (∋∙-∋='-≢ inΓ1 inΓ2)
∋∙-∋='-≢ (S, inΓ1) (S, inΓ2) = ∋∙-∋='-≢ inΓ1 inΓ2
∋∙-∋='-≢ (S⋈ inΓ1) (S⋈ inΓ2) = ∋∙-∋='-≢ inΓ1 inΓ2

⊢r-¬ε : Γ ⊢r A
        → Γ ∋=' k
        → k ¬ε A
⊢r-¬ε ⊢r-int inΓ = ¬ε-int
⊢r-¬ε (⊢r-var-∙ inΓ₁) inΓ = ¬ε-var (∋∙-∋='-≢ inΓ inΓ₁)
⊢r-¬ε (⊢r-arr regA regA₁) inΓ = ¬ε-arr (⊢r-¬ε regA inΓ) (⊢r-¬ε regA₁ inΓ)
⊢r-¬ε (⊢r-∀ regA) inΓ = ¬ε-∀ (⊢r-¬ε regA (S∙ inΓ))


↑ty-var-inv : ∀ {m} {X Y : Fin m} {re k : Fin (1 + m)}
               → ‶ X ↑ty k ⇘ ‶ re
               → re ≡ punchIn k Y
               → X ≡ Y
↑ty-var-inv {X = X} {Y = Y} {k = k} ↑ty-var eq = punchIn-injective k X Y eq

s-strengthen= : Γ ⊢ j # A' ⌞ ≤ ⌝ B'
              → Γ ◀ k =⇘ Γ'
              → A ↑ty k ⇘ A'
              → B ↑ty k ⇘ B'
              → Γ' ⊢ j # A ⌞ ≤ ⌝ B
s-strengthen= (s-refl regΔ cloA grd) newΓ upA upB = s-refl (sregular-strengthen= regΔ newΓ)
                                                           (⊢c-strengthen= cloA newΓ upA)
                                                           (≫-strengthen= grd newΓ upA upB)
s-strengthen= (s-int regΔ) newΓ ↑ty-int ↑ty-int = s-int (sregular-strengthen= regΔ newΓ)
s-strengthen= {B = ‶ X} (s-var-∙ regΔ inΔ) newΓ ↑ty-var upB with refl ← ↑ty-var-inv upB refl
  = s-var-∙ (sregular-strengthen= regΔ newΓ) (∋∙-strengthen= inΔ newΓ)
s-strengthen= (s-arr₁ s s₁) newΓ (↑ty-arr upA upA₁) (↑ty-arr upB upB₁) = s-arr₁ (s-strengthen= s newΓ upB upA)
                                                                                (s-strengthen= s₁ newΓ upA₁ upB₁)
s-strengthen= (s-arr₂ s s₁) newΓ (↑ty-arr upA upA₁) (↑ty-arr upB upB₁) = s-arr₂ (s-strengthen= s newΓ upB upA)
                                                                                (s-strengthen= s₁ newΓ upA₁ upB₁)
s-strengthen= (s-arr₃ cloA grd s) newΓ (↑ty-arr upA upA₁) (↑ty-arr upB upB₁) = s-arr₃ (⊢c-strengthen= cloA newΓ upA)
                                                                                      (≫-strengthen= grd newΓ upA upB)
                                                                                      (s-strengthen= s newΓ upA₁ upB₁)
s-strengthen= (s-∀ s) newΓ (↑ty-∀ upA) (↑ty-∀ upB) = s-∀ (s-strengthen= s (◀S∙ newΓ) upA upB)
s-strengthen= (s-∀l {B = B} s ic fd upC upD) newΓ (↑ty-∀ upA) (↑ty-arr {A = A′} {B = B′} upB upB₁)
  with ⟨ A″ , upA′ ⟩ ← ↑ty0-total A′
  with ⟨ B″ , upB′ ⟩ ← ↑ty0-total B′
  with reg-S= regΓ regA ← s-sregular s
  with k¬εB ← ⊢r-¬ε regA (◀=-∋=' newΓ)
  with ⟨ preB , upB' ⟩ ← ↑ty-surjective k¬εB
    = s-∀l (s-strengthen= s (◀S= newΓ upB') upA
      (↑ty-arr (↑ty-comm0' upB upC upA′) (↑ty-comm0' upB₁ upD upB′))) ic (↑ty-find0' fd upA) upA′ upB′
s-strengthen= (s-svar-l x inΔ) newΓ ↑ty-var upB = s-svar-l (sregular-strengthen= x newΓ) {!!}
s-strengthen= (s-svar-r x inΔ) newΓ upA ↑ty-var = s-svar-r (sregular-strengthen= x newΓ) {!!}
