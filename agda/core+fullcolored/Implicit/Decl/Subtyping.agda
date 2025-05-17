module Implicit.Decl.Subtyping where

open import Implicit.Language.All

----------------------------------------------------------------------
--+                           Subtyping                            +--
----------------------------------------------------------------------

infix 3 _⊢_#_≤_
data _⊢_#_≤_ : Env n m → Counter m → Type m → Type m → Set where
  s-refl :
      (regΔ : SRegular Δ)
    → (cloA : Δ ⊢r A)
    → Δ ⊢ Z # A ≤ A
  s-int :
      (regΔ : SRegular Δ)
    → Δ ⊢ ∞ # Int ≤ Int
  s-var-∙ :
      (regΔ : SRegular Δ)
    → (inΔ : Δ ∋∙ X)
    → Δ ⊢ ∞ # ‶ X ≤ ‶ X
  s-arr₁ :
      Δ ⊢ ∞ # C ≤ A
    → Δ ⊢ ∞ # B ≤ D
    → Δ ⊢ ∞ # A `→ B ≤ C `→ D
  s-arr₂ :
      Δ ⊢ ∞ # C ≤ A
    → Δ ⊢ j # B ≤ D
    → Δ ⊢ 𝕚 j # A `→ B ≤ C `→ D
  s-arr₃ :
      (regA : Δ ⊢r A)
    → Δ ⊢ j # B ≤ D
    → Δ ⊢ 𝕔 j # A `→ B ≤ A `→ D
  s-∀ :
      Δ ,∙ ⊢ ∞ # A ≤ B
    → Δ ⊢ ∞ # `∀ A ≤ `∀ B
  s-∀l :
      (regB : Γ ⊢r B)
    → (st : ⟦ B ⟧ A ⇘ A*)
    → Γ ⊢ j # A* ≤ C `→ D
    → (ic : (𝕚𝕔 j))
    → (fd : find A #0 j')
    → (upj : ↑tyʲ0 j ⇘ j')
    → Γ ⊢ j # `∀ A ≤ C `→ D
  s-tapp :
      (regB : Δ ⊢r B)
    → (st : ⟦ B ⟧ A ⇘ A*)
    → Δ ⊢ j # A* ≤ C
    → (upC : ↑ty0 C ⇘ C')
    → Δ ⊢ 𝕋₍ B ₎ j # `∀ A ≤ `∀ C'



s1-⊢r-l : Γ ⊢ j # A ≤ B
        → Γ ⊢r A

s1-⊢r-r : Γ ⊢ j # A ≤ B
        → Γ ⊢r B

s1-⊢r-l (s-refl regΔ cloA) = cloA
s1-⊢r-l (s-int regΔ) = ⊢r-int
s1-⊢r-l (s-var-∙ regΔ inΔ) = ⊢r-var-∙ inΔ
s1-⊢r-l (s-arr₁ s s₁) = ⊢r-arr (s1-⊢r-r s) (s1-⊢r-l s₁)
s1-⊢r-l (s-arr₂ s s₁) = ⊢r-arr (s1-⊢r-r s) (s1-⊢r-l s₁)
s1-⊢r-l (s-arr₃ regA s) = ⊢r-arr regA (s1-⊢r-l s)
s1-⊢r-l (s-∀ s) = ⊢r-∀ (s1-⊢r-l s)
s1-⊢r-l (s-∀l regB st s ic fd upj) = st0-⊢r' (s1-⊢r-l s) regB st
s1-⊢r-l (s-tapp regB st s upC) = st0-⊢r' (s1-⊢r-l s) regB st

s1-⊢r-r (s-refl regΔ cloA) = cloA
s1-⊢r-r (s-int regΔ) = ⊢r-int
s1-⊢r-r (s-var-∙ regΔ inΔ) = ⊢r-var-∙ inΔ
s1-⊢r-r (s-arr₁ s s₁) = ⊢r-arr (s1-⊢r-l s) (s1-⊢r-r s₁)
s1-⊢r-r (s-arr₂ s s₁) = ⊢r-arr (s1-⊢r-l s) (s1-⊢r-r s₁)
s1-⊢r-r (s-arr₃ regA s) = ⊢r-arr regA (s1-⊢r-r s)
s1-⊢r-r (s-∀ s) = ⊢r-∀ (s1-⊢r-r s)
s1-⊢r-r (s-∀l regB st s ic fd upj) = s1-⊢r-r s
s1-⊢r-r (s-tapp regB st s upC) = ⊢r-∀ (⊢r-weaken∙0 (s1-⊢r-r s) upC)


s1-strengthen= : Γ ⊢ j' # A' ≤ B'
              → Γ ◀ k =⇘ Γ'
              → A ↑ty k ⇘ A'
              → B ↑ty k ⇘ B'
              → j ↑tyʲ k ⇘ j'
              → Γ' ⊢ j # A ≤ B
s1-strengthen= (s-refl regΔ cloA) new upA upB ↑tyʲ-Z
  with refl ← ↑ty-unique-inver upA upB = s-refl (sregular-strengthen= regΔ new) (⊢r-strengthen= cloA new upB)
s1-strengthen= (s-int regΔ) new ↑ty-int ↑ty-int ↑tyʲ-∞ = s-int (sregular-strengthen= regΔ new)
s1-strengthen= {B = ‶ X} (s-var-∙ regΔ inΔ) new ↑ty-var upB ↑tyʲ-∞
  with refl ← ↑ty-var-inv upB refl = s-var-∙ (sregular-strengthen= regΔ new) (∋∙-strengthen= inΔ new)
s1-strengthen= (s-arr₁ s s₁) new (↑ty-arr upA upA₁) (↑ty-arr upB upB₁) ↑tyʲ-∞
  = s-arr₁ (s1-strengthen= s new upB upA ↑tyʲ-∞) (s1-strengthen= s₁ new upA₁ upB₁ ↑tyʲ-∞)
s1-strengthen= (s-arr₂ s s₁) new (↑ty-arr upA upA₁) (↑ty-arr upB upB₁) (↑tyʲ-𝕚 upj)
  = s-arr₂ (s1-strengthen= s new upB upA ↑tyʲ-∞) (s1-strengthen= s₁ new upA₁ upB₁ upj)
s1-strengthen= (s-arr₃ regA s) new (↑ty-arr upA upA₁) (↑ty-arr upB upB₁) (↑tyʲ-𝕔 upj)
  with refl ← ↑ty-unique-inver upA upB
  = s-arr₃ (⊢r-strengthen= regA new upB) (s1-strengthen= s new upA₁ upB₁ upj)
s1-strengthen= (s-∀ s) new (↑ty-∀ upA) (↑ty-∀ upB) ↑tyʲ-∞ = s-∀ (s1-strengthen= s (◀S∙ new) upA upB ↑tyʲ-∞)
s1-strengthen= {j = j} (s-∀l {B = B} {A* = A*} regB st s ic fd upj₁) new (↑ty-∀ upA) (↑ty-arr upB upB₁) upj
  with ⟨ j' , upj' ⟩ ← ↑tyʲ0-total j
  with regA* ← s1-⊢r-l s
  with k¬εA* ← ⊢r-¬ε regA* (◀=-∋=' new)
  with ⟨ preA* , upA* ⟩ ← ↑ty-surjective k¬εA*
  with k¬εB ← ⊢r-¬ε regB (◀=-∋=' new)
  with ⟨ preB , upB' ⟩ ← ↑ty-surjective k¬εB
  = s-∀l (⊢r-strengthen= regB new upB')
         (↑ty-st-comm0'' st upB' upA upA*)
         (s1-strengthen= s new upA* (↑ty-arr upB upB₁) upj) (𝕚𝕔-↑tyʲ' ic upj) (↑ty-find0' fd upA (↑tyʲ-comm0' upj upj₁ upj')) upj'
s1-strengthen= (s-tapp {A* = A*} {C = C} regB st s upC) new (↑ty-∀ upA) (↑ty-∀ upB) (↑tyʲ-𝕋 {j = j} upj upA₁)
  with regA* ← s1-⊢r-l s
  with regC ← s1-⊢r-r s
  with k¬εA* ← ⊢r-¬ε regA* (◀=-∋=' new)
  with k¬εC ← ⊢r-¬ε regC (◀=-∋=' new)
  with ⟨ preA* , upA* ⟩ ← ↑ty-surjective k¬εA*
  with ⟨ preC , upC' ⟩ ← ↑ty-surjective k¬εC
  = s-tapp (⊢r-strengthen= regB new upA₁) (↑ty-st-comm0'' st upA₁ upA upA*) (s1-strengthen= s new upA* upC' upj) (↑ty-comm1 upB upC upC')

s1-strengthen=0 : Γ ,= T ⊢ j' # A' ≤ B'
            → ↑ty0 A ⇘ A'
            → ↑ty0 B ⇘ B'
            → ↑tyʲ0 j ⇘ j'
            → Γ ⊢ j # A ≤ B
s1-strengthen=0 s upA upB upj = s1-strengthen= s ◀Z upA upB upj

s1-weaken, : Γ ⊢ j # A ≤ B
          → Γ ▶s k , T ⇘ Γ'
          → Γ' ⊢ j # A ≤ B
s1-weaken, (s-refl regΔ cloA) new = s-refl (sregular-weaken,s regΔ new) (⊢r-weaken,s cloA new)
s1-weaken, (s-int regΔ) new = s-int (sregular-weaken,s regΔ new)
s1-weaken, (s-var-∙ regΔ inΔ) new = s-var-∙ (sregular-weaken,s regΔ new) (∋∙-weaken,s inΔ new)
s1-weaken, (s-arr₁ s s₁) new = s-arr₁ (s1-weaken, s new) (s1-weaken, s₁ new)
s1-weaken, (s-arr₂ s s₁) new = s-arr₂ (s1-weaken, s new) (s1-weaken, s₁ new)
s1-weaken, (s-arr₃ regA s) new = s-arr₃ (⊢r-weaken,s regA new) (s1-weaken, s new)
s1-weaken, {T = T} (s-∀ s) new
  with ⟨ T , upT ⟩ ← ↑ty0-total T = s-∀ (s1-weaken, s (▶sS∙ new upT))
s1-weaken, (s-∀l regB st s ic fd upj) new = s-∀l (⊢r-weaken,s regB new) st (s1-weaken, s new) ic fd upj
s1-weaken, (s-tapp regB st s upC) new = s-tapp (⊢r-weaken,s regB new) st (s1-weaken, s new) upC


s1-weaken,0 : Γ ⋈ ⊢ j # A ≤ B
            → Γ ⊢r T
            → Γ , T ⋈ ⊢ j # A ≤ B
s1-weaken,0 s regT = s1-weaken, s (▶sS⋈ (▶Z regT))
