module Implicit.Decl.Subtyping where

open import Implicit.Language.All

----------------------------------------------------------------------
--+                           Subtyping                            +--
----------------------------------------------------------------------

infix 3 _⊢d_#_≤_
data _⊢d_#_≤_ : Env n m → Mask → Type m → Type m → Set where
  s-refl :
      (regΔ : SRegular Δ)
    → (cloA : Δ ⊢r A)
    → Δ ⊢d `■ # A ≤ A
  s-int :
      (regΔ : SRegular Δ)
    → Δ ⊢d `□ # Int ≤ Int
  s-var-∙ :
      (regΔ : SRegular Δ)
    → (inΔ : Δ ∋∙ X)
    → Δ ⊢d `□ # ‶ X ≤ ‶ X
  s-arr₁ :
      Δ ⊢d `□ # C ≤ A
    → Δ ⊢d `□ # B ≤ D
    → Δ ⊢d `□ # A `→ B ≤ C `→ D
  s-arr₂ :
      Δ ⊢d `□ # C ≤ A
    → Δ ⊢d j # B ≤ D
    → Δ ⊢d □ · j # A `→ B ≤ C `→ D
  s-arr₃ :
      (regA : Δ ⊢r A)
    → Δ ⊢d j # B ≤ D
    → Δ ⊢d ■ · j # A `→ B ≤ A `→ D
  s-∀ :
      Δ ,∙ ⊢d `□ # A ≤ B
    → Δ ⊢d `□ # `∀ A ≤ `∀ B
  s-∀l :
      (regB : Γ ⊢r B)
    → (st : ⟦ B ⟧ A ⇘ A*)
    → Γ ⊢d (i · j) # A* ≤ C `→ D
    → (fd : find A #0 (i · j))
    → Γ ⊢d (i · j) # `∀ A ≤ C `→ D
  s-∀l-no-appear :
      (regB : Γ ⊢r B)
    → (st : ⟦ B ⟧ A ⇘ A*)
    → Γ ⊢d (i · j) # A* ≤ C `→ D
    → (fd : #0 ¬ε A)
    → Γ ⊢d (i · j) # `∀ A ≤ C `→ D



s1-⊢r-l : Γ ⊢d j # A ≤ B
        → Γ ⊢r A

s1-⊢r-r : Γ ⊢d j # A ≤ B
        → Γ ⊢r B

s1-⊢r-l (s-refl regΔ cloA) = cloA
s1-⊢r-l (s-int regΔ) = ⊢r-int
s1-⊢r-l (s-var-∙ regΔ inΔ) = ⊢r-var-∙ inΔ
s1-⊢r-l (s-arr₁ s s₁) = ⊢r-arr (s1-⊢r-r s) (s1-⊢r-l s₁)
s1-⊢r-l (s-arr₂ s s₁) = ⊢r-arr (s1-⊢r-r s) (s1-⊢r-l s₁)
s1-⊢r-l (s-arr₃ regA s) = ⊢r-arr regA (s1-⊢r-l s)
s1-⊢r-l (s-∀ s) = ⊢r-∀ (s1-⊢r-l s)
s1-⊢r-l (s-∀l regB st s fd) = st0-⊢r' (s1-⊢r-l s) regB st
s1-⊢r-l (s-∀l-no-appear regB st s fd) = st0-⊢r' (s1-⊢r-l s) regB st

s1-⊢r-r (s-refl regΔ cloA) = cloA
s1-⊢r-r (s-int regΔ) = ⊢r-int
s1-⊢r-r (s-var-∙ regΔ inΔ) = ⊢r-var-∙ inΔ
s1-⊢r-r (s-arr₁ s s₁) = ⊢r-arr (s1-⊢r-l s) (s1-⊢r-r s₁)
s1-⊢r-r (s-arr₂ s s₁) = ⊢r-arr (s1-⊢r-l s) (s1-⊢r-r s₁)
s1-⊢r-r (s-arr₃ regA s) = ⊢r-arr regA (s1-⊢r-r s)
s1-⊢r-r (s-∀ s) = ⊢r-∀ (s1-⊢r-r s)
s1-⊢r-r (s-∀l regB st s fd) = s1-⊢r-r s
s1-⊢r-r (s-∀l-no-appear regB st s fd) = s1-⊢r-r s

s1-strengthen= : Γ ⊢d j # A' ≤ B'
              → Γ ◀ k =⇘ Γ'
              → A ↑ty k ⇘ A'
              → B ↑ty k ⇘ B'
              → Γ' ⊢d j # A ≤ B
s1-strengthen= (s-refl regΔ cloA) new upA upB
  with refl ← ↑ty-unique-inver upA upB = s-refl (sregular-strengthen= regΔ new) (⊢r-strengthen= cloA new upB)
s1-strengthen= (s-int regΔ) new ↑ty-int ↑ty-int = s-int (sregular-strengthen= regΔ new)
s1-strengthen= {B = ‶ X} (s-var-∙ regΔ inΔ) new ↑ty-var upB
  with refl ← ↑ty-var-inv upB refl = s-var-∙ (sregular-strengthen= regΔ new) (∋∙-strengthen= inΔ new)
s1-strengthen= (s-arr₁ s s₁) new (↑ty-arr upA upA₁) (↑ty-arr upB upB₁)
  = s-arr₁ (s1-strengthen= s new upB upA) (s1-strengthen= s₁ new upA₁ upB₁)
s1-strengthen= (s-arr₂ s s₁) new (↑ty-arr upA upA₁) (↑ty-arr upB upB₁)
  = s-arr₂ (s1-strengthen= s new upB upA) (s1-strengthen= s₁ new upA₁ upB₁)
s1-strengthen= (s-arr₃ regA s) new (↑ty-arr upA upA₁) (↑ty-arr upB upB₁)
  with refl ← ↑ty-unique-inver upA upB
  = s-arr₃ (⊢r-strengthen= regA new upB) (s1-strengthen= s new upA₁ upB₁)
s1-strengthen= (s-∀ s) new (↑ty-∀ upA) (↑ty-∀ upB) = s-∀ (s1-strengthen= s (◀S∙ new) upA upB)
s1-strengthen= {j = j} (s-∀l {B = B} {A* = A*} regB st s fd) new (↑ty-∀ upA) (↑ty-arr upB upB₁)
  with regA* ← s1-⊢r-l s
  with k¬εA* ← ⊢r-¬ε regA* (◀=-∋=' new)
  with ⟨ preA* , upA* ⟩ ← ↑ty-surjective k¬εA*
  with k¬εB ← ⊢r-¬ε regB (◀=-∋=' new)
  with ⟨ preB , upB' ⟩ ← ↑ty-surjective k¬εB
  = s-∀l (⊢r-strengthen= regB new upB')
         (↑ty-st-comm0'' st upB' upA upA*)
         (s1-strengthen= s new upA* (↑ty-arr upB upB₁)) (↑ty-find0' fd upA)
s1-strengthen= (s-∀l-no-appear {B = B} {A* = A*} regB st s fd) new (↑ty-∀ upA) (↑ty-arr upB upB₁)
  with regA* ← s1-⊢r-l s
  with k¬εA* ← ⊢r-¬ε regA* (◀=-∋=' new)
  with ⟨ preA* , upA* ⟩ ← ↑ty-surjective k¬εA*
  with k¬εB ← ⊢r-¬ε regB (◀=-∋=' new)
  with ⟨ preB , upB' ⟩ ← ↑ty-surjective k¬εB
  = s-∀l-no-appear (⊢r-strengthen= regB new upB')
         (↑ty-st-comm0'' st upB' upA upA*)
         (s1-strengthen= s new upA* (↑ty-arr upB upB₁)) (¬ε-↑ty'-inv0 fd upA)

s1-strengthen=0 : Γ ,= T ⊢d j # A' ≤ B'
            → ↑ty0 A ⇘ A'
            → ↑ty0 B ⇘ B'
            → Γ ⊢d j # A ≤ B
s1-strengthen=0 s upA upB = s1-strengthen= s ◀Z upA upB


s1-weaken, : Γ ⊢d j # A ≤ B
          → Γ ▶s k , T ⇘ Γ'
          → Γ' ⊢d j # A ≤ B
s1-weaken, (s-refl regΔ cloA) new = s-refl (sregular-weaken,s regΔ new) (⊢r-weaken,s cloA new)
s1-weaken, (s-int regΔ) new = s-int (sregular-weaken,s regΔ new)
s1-weaken, (s-var-∙ regΔ inΔ) new = s-var-∙ (sregular-weaken,s regΔ new) (∋∙-weaken,s inΔ new)
s1-weaken, (s-arr₁ s s₁) new = s-arr₁ (s1-weaken, s new) (s1-weaken, s₁ new)
s1-weaken, (s-arr₂ s s₁) new = s-arr₂ (s1-weaken, s new) (s1-weaken, s₁ new)
s1-weaken, (s-arr₃ regA s) new = s-arr₃ (⊢r-weaken,s regA new) (s1-weaken, s new)
s1-weaken, {T = T} (s-∀ s) new
  with ⟨ T , upT ⟩ ← ↑ty0-total T = s-∀ (s1-weaken, s (▶sS∙ new upT))
s1-weaken, (s-∀l regB st s fd) new = s-∀l (⊢r-weaken,s regB new) st (s1-weaken, s new) fd
s1-weaken, (s-∀l-no-appear regB st s fd) new = s-∀l-no-appear (⊢r-weaken,s regB new) st (s1-weaken, s new) fd


s1-weaken,0 : Γ ⋈ ⊢d j # A ≤ B
            → Γ ⊢r T
            → Γ , T ⋈ ⊢d j # A ≤ B
s1-weaken,0 s regT = s1-weaken, s (▶sS⋈ (▶Z regT))



s1-strengthen^ : Γ ⊢d j # A' ≤ B'
              → Γ ◀ k ^⇘ Γ'
              → A ↑ty k ⇘ A'
              → B ↑ty k ⇘ B'
              → Γ' ⊢d j # A ≤ B
s1-strengthen^ (s-refl regΔ cloA) new upA upB
  with refl ← ↑ty-unique-inver upA upB = s-refl (sregular-strengthen^ regΔ new) (⊢r-strengthen^ cloA new upB)
s1-strengthen^ (s-int regΔ) new ↑ty-int ↑ty-int = s-int (sregular-strengthen^ regΔ new)
s1-strengthen^ {B = ‶ X} (s-var-∙ regΔ inΔ) new ↑ty-var upB
  with refl ← ↑ty-var-inv upB refl = s-var-∙ (sregular-strengthen^ regΔ new) (∋∙-strengthen^ inΔ new)
s1-strengthen^ (s-arr₁ s s₁) new (↑ty-arr upA upA₁) (↑ty-arr upB upB₁)
  = s-arr₁ (s1-strengthen^ s new upB upA) (s1-strengthen^ s₁ new upA₁ upB₁)
s1-strengthen^ (s-arr₂ s s₁) new (↑ty-arr upA upA₁) (↑ty-arr upB upB₁)
  = s-arr₂ (s1-strengthen^ s new upB upA) (s1-strengthen^ s₁ new upA₁ upB₁)
s1-strengthen^ (s-arr₃ regA s) new (↑ty-arr upA upA₁) (↑ty-arr upB upB₁)
  with refl ← ↑ty-unique-inver upA upB
  = s-arr₃ (⊢r-strengthen^ regA new upB) (s1-strengthen^ s new upA₁ upB₁)
s1-strengthen^ (s-∀ s) new (↑ty-∀ upA) (↑ty-∀ upB) = s-∀ (s1-strengthen^ s (◀S∙ new) upA upB)
s1-strengthen^ {j = j} (s-∀l {B = B} {A* = A*} regB st s fd) new (↑ty-∀ upA) (↑ty-arr upB upB₁)
  with regA* ← s1-⊢r-l s
  with k¬εA* ← ⊢r-¬ε-^ regA* (◀^-∋^' new)
  with ⟨ preA* , upA* ⟩ ← ↑ty-surjective k¬εA*
  with k¬εB ← ⊢r-¬ε-^ regB (◀^-∋^' new)
  with ⟨ preB , upB' ⟩ ← ↑ty-surjective k¬εB
  = s-∀l (⊢r-strengthen^ regB new upB')
         (↑ty-st-comm0'' st upB' upA upA*)
         (s1-strengthen^ s new upA* (↑ty-arr upB upB₁)) (↑ty-find0' fd upA)
s1-strengthen^ (s-∀l-no-appear {B = B} {A* = A*} regB st s fd) new (↑ty-∀ upA) (↑ty-arr upB upB₁)
  with regA* ← s1-⊢r-l s
  with k¬εA* ← ⊢r-¬ε-^ regA* (◀^-∋^' new)
  with ⟨ preA* , upA* ⟩ ← ↑ty-surjective k¬εA*
  with k¬εB ← ⊢r-¬ε-^ regB (◀^-∋^' new)
  with ⟨ preB , upB' ⟩ ← ↑ty-surjective k¬εB
  = s-∀l-no-appear (⊢r-strengthen^ regB new upB')
         (↑ty-st-comm0'' st upB' upA upA*)
         (s1-strengthen^ s new upA* (↑ty-arr upB upB₁)) (¬ε-↑ty'-inv0 fd upA)

s1-strengthen^0 : Γ ,^ ⊢d j # A' ≤ B'
            → ↑ty0 A ⇘ A'
            → ↑ty0 B ⇘ B'
            → Γ ⊢d j # A ≤ B
s1-strengthen^0 s upA upB = s1-strengthen^ s ◀Z upA upB
