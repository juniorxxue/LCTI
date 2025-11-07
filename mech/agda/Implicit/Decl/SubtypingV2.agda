module Implicit.Decl.SubtypingV2 where
-- small tweaks for better alignment with intermediate system

open import Implicit.Language.All

----------------------------------------------------------------------
--+                           Subtyping                            +--
----------------------------------------------------------------------

infix 3 _⊢d²_#_≤_
data _⊢d²_#_≤_ : Env n m → Mask → Type m → Type m → Set where
  s-refl :
      (regΔ : SRegular Δ)
    → (cloA : Δ ⊢r A)
    → Δ ⊢d² `■ # A ≤ A
  s-int :
      (regΔ : SRegular Δ)
    → Δ ⊢d² `□ # Int ≤ Int
  s-var-∙ :
      (regΔ : SRegular Δ)
    → (inΔ : Δ ∋∙ X)
    → Δ ⊢d² `□ # ‶ X ≤ ‶ X
  s-arr₁ :
      Δ ⊢d² `□ # C ≤ A
    → Δ ⊢d² `□ # B ≤ D
    → Δ ⊢d² `□ # A `→ B ≤ C `→ D
  s-arr₂ :
      Δ ⊢d² `□ # C ≤ A
    → Δ ⊢d² j # B ≤ D
    → Δ ⊢d² □ · j # A `→ B ≤ C `→ D
  s-arr₃ :
      (regA : Δ ⊢r A)
    → Δ ⊢d² j # B ≤ D
    → Δ ⊢d² ■ · j # A `→ B ≤ A `→ D
  s-∀ :
      Δ ,∙ ⊢d² `□ # A ≤ B
    → Δ ⊢d² `□ # `∀ A ≤ `∀ B
  s-∀l :
      (grd : (Γ ,= B) ≫ A ⇘ A%)
    → (regA : Γ ,∙ ⊢r A)
    → Γ ,= B ⊢d² (i · j) # A% ≤ C' `→ D'
    → (fd : find A #0 (i · j))
    → (upC : ↑ty0 C ⇘ C')
    → (upD : ↑ty0 D ⇘ D')
    → Γ ⊢d² (i · j) # `∀ A ≤ C `→ D
  s-∀l-no-appear :
      (grd : (Γ ,^) ≫ A ⇘ A%)
    → (regA : Γ ,∙ ⊢r A)
    → Γ ,^ ⊢d² (i · j) # A% ≤ C' `→ D'
    → (fd : #0 ¬ε A)
    → (upC : ↑ty0 C ⇘ C')
    → (upD : ↑ty0 D ⇘ D')
    → Γ ⊢d² (i · j) # `∀ A ≤ C `→ D

s2-sregular : Γ ⊢d² j # A ≤ B
            → SRegular Γ
s2-sregular (s-refl regΔ cloA) = regΔ
s2-sregular (s-int regΔ) = regΔ
s2-sregular (s-var-∙ regΔ inΔ) = regΔ
s2-sregular (s-arr₁ s s₁) = s2-sregular s
s2-sregular (s-arr₂ s s₁) = s2-sregular s
s2-sregular (s-arr₃ regA s) = s2-sregular s
s2-sregular (s-∀ s) with s2-sregular s
... | reg-S∙ r = r
s2-sregular (s-∀l grd regA s fd upC upD) with s2-sregular s
... | reg-S= r regA = r
s2-sregular (s-∀l-no-appear grd regA s fd upC upD) with s2-sregular s
... | reg-S^ r = r


s2-⊢r-l : Γ ⊢d² j # A ≤ B
        → Γ ⊢r A

s2-⊢r-r : Γ ⊢d² j # A ≤ B
         → Γ ⊢r B


s2-⊢r-l (s-refl regΔ cloA) = cloA
s2-⊢r-l (s-int regΔ) = ⊢r-int
s2-⊢r-l (s-var-∙ regΔ inΔ) = ⊢r-var-∙ inΔ
s2-⊢r-l (s-arr₁ s s₁) = ⊢r-arr (s2-⊢r-r s) (s2-⊢r-l s₁)
s2-⊢r-l (s-arr₂ s s₁) = ⊢r-arr (s2-⊢r-r s) (s2-⊢r-l s₁)
s2-⊢r-l (s-arr₃ regA s) = ⊢r-arr regA (s2-⊢r-l s)
s2-⊢r-l (s-∀ s) = ⊢r-∀ (s2-⊢r-l s)
s2-⊢r-l (s-∀l grd regA s fd upC upD) = ⊢r-∀ regA
s2-⊢r-l (s-∀l-no-appear grd regA s fd upC upD) = ⊢r-∀ regA

s2-⊢r-r (s-refl regΔ cloA) = cloA
s2-⊢r-r (s-int regΔ) = ⊢r-int
s2-⊢r-r (s-var-∙ regΔ inΔ) = ⊢r-var-∙ inΔ
s2-⊢r-r (s-arr₁ s s₁) = ⊢r-arr (s2-⊢r-l s) (s2-⊢r-r s₁)
s2-⊢r-r (s-arr₂ s s₁) = ⊢r-arr (s2-⊢r-l s) (s2-⊢r-r s₁)
s2-⊢r-r (s-arr₃ regA s) = ⊢r-arr regA (s2-⊢r-r s)
s2-⊢r-r (s-∀ s) = ⊢r-∀ (s2-⊢r-r s)
s2-⊢r-r (s-∀l grd regA s fd upC upD) = ⊢r-strengthen=0 (s2-⊢r-r s) (↑ty-arr upC upD)
s2-⊢r-r (s-∀l-no-appear grd regA s fd upC upD) = ⊢r-strengthen^0 (s2-⊢r-r s) (↑ty-arr upC upD)

s2-weaken= : Γ ⊢d² j # A ≤ B
           → Γ ▶ k ,= T ⇘ Γ'
            → A ↑ty k ⇘ A'
            → B ↑ty k ⇘ B'
            → Γ' ⊢d² j # A' ≤ B'
s2-weaken= (s-refl regΔ cloA) new upA upB
  with refl ← ↑ty-unique upA upB = s-refl (sregular-weaken= regΔ new) (⊢r-weaken= cloA new upB)
s2-weaken= (s-int regΔ) new ↑ty-int ↑ty-int = s-int (sregular-weaken= regΔ new)
s2-weaken= (s-var-∙ regΔ inΔ) new ↑ty-var ↑ty-var = s-var-∙ (sregular-weaken= regΔ new) (∋∙-weaken= inΔ new)
s2-weaken= (s-arr₁ s s₁) new (↑ty-arr upA upA₁) (↑ty-arr upB upB₁) = s-arr₁ (s2-weaken= s new upB upA) (s2-weaken= s₁ new upA₁ upB₁)
s2-weaken= (s-arr₂ s s₁) new (↑ty-arr upA upA₁) (↑ty-arr upB upB₁)
  = s-arr₂ (s2-weaken= s new upB upA) (s2-weaken= s₁ new upA₁ upB₁)
s2-weaken= (s-arr₃ regA s) new (↑ty-arr upA upA₁) (↑ty-arr upB upB₁)
  with refl ← ↑ty-unique upA upB = s-arr₃ (⊢r-weaken= regA new upB) (s2-weaken= s new upA₁ upB₁)
s2-weaken= {T = T} (s-∀ s) new (↑ty-∀ upA) (↑ty-∀ upB)
  with ⟨ T' , upT ⟩ ← ↑ty0-total T = s-∀ (s2-weaken= s (▶S∙ new upT) upA upB)
s2-weaken= {k = k} {T = T} (s-∀l {B = B} {A% = A%} grd regA s fd upC upD) new (↑ty-∀ upA) (↑ty-arr {A' = C'} {B' = D'} upB upB₁)
  with ⟨ T' , upT ⟩ ← ↑ty0-total T
  with ⟨ B' , upB₂ ⟩ ← ↑ty-total B k
  with ⟨ C₁ , upC₁ ⟩ ← ↑ty0-total C'
  with ⟨ D₁ , upD₁ ⟩ ← ↑ty0-total D'
  with ⟨ A%' , upA% ⟩ ← ↑ty-total A% (#S k)
  = s-∀l (≫-weaken= grd (▶S= new upT upB₂) upA upA%)
         (⊢r-weaken= regA (▶S∙ new upT) upA)
         (s2-weaken= s (▶S= new upT upB₂) upA% (↑ty-arr (↑ty-comm0' upB upC₁ upC) (↑ty-comm0' upB₁ upD₁ upD)))
         (↑ty-find0 fd upA) upC₁ upD₁
s2-weaken= {k = k} {T = T} (s-∀l-no-appear {A% = A%} grd regA s fd upC upD) new (↑ty-∀ upA) (↑ty-arr {A' = C'} {B' = D'} upB upB₁)
  with ⟨ T' , upT ⟩ ← ↑ty0-total T
--  with ⟨ B' , upB₂ ⟩ ← ↑ty-total B k
  with ⟨ C₁ , upC₁ ⟩ ← ↑ty0-total C'
  with ⟨ D₁ , upD₁ ⟩ ← ↑ty0-total D'
  with ⟨ A%' , upA% ⟩ ← ↑ty-total A% (#S k)
  = s-∀l-no-appear (≫-weaken= grd (▶S^ new upT) upA upA%)
         (⊢r-weaken= regA (▶S∙ new upT) upA)
         (s2-weaken= s (▶S^ new upT) upA% (↑ty-arr (↑ty-comm0' upB upC₁ upC) (↑ty-comm0' upB₁ upD₁ upD)))
         (¬ε-↑ty0' fd upA) upC₁ upD₁

s2-weaken=0 : Γ ⊢d² j # A ≤ B
            → ↑ty0 A ⇘ A'
            → ↑ty0 B ⇘ B'
            → Γ ⊢r T
            → Γ ,= T ⊢d² j # A' ≤ B'
s2-weaken=0 s upA upB regT = s2-weaken= s (▶Z regT) upA upB


s2-weaken^ : Γ ⊢d² j # A ≤ B
           → Γ ▶ k ,^⇘ Γ'
            → A ↑ty k ⇘ A'
            → B ↑ty k ⇘ B'
            → Γ' ⊢d² j # A' ≤ B'
s2-weaken^ (s-refl regΔ cloA) new upA upB
  with refl ← ↑ty-unique upA upB = s-refl (sregular-weaken^ regΔ new) (⊢r-weaken^ cloA new upB)
s2-weaken^ (s-int regΔ) new ↑ty-int ↑ty-int  = s-int (sregular-weaken^ regΔ new)
s2-weaken^ (s-var-∙ regΔ inΔ) new ↑ty-var ↑ty-var  = s-var-∙ (sregular-weaken^ regΔ new) (∋∙-weaken^ inΔ new)
s2-weaken^ (s-arr₁ s s₁) new (↑ty-arr upA upA₁) (↑ty-arr upB upB₁)  = s-arr₁ (s2-weaken^ s new upB upA) (s2-weaken^ s₁ new upA₁ upB₁)
s2-weaken^ (s-arr₂ s s₁) new (↑ty-arr upA upA₁) (↑ty-arr upB upB₁)
  = s-arr₂ (s2-weaken^ s new upB upA) (s2-weaken^ s₁ new upA₁ upB₁)
s2-weaken^ (s-arr₃ regA s) new (↑ty-arr upA upA₁) (↑ty-arr upB upB₁)
  with refl ← ↑ty-unique upA upB = s-arr₃ (⊢r-weaken^ regA new upB) (s2-weaken^ s new upA₁ upB₁)
s2-weaken^ (s-∀ s) new (↑ty-∀ upA) (↑ty-∀ upB) = s-∀ (s2-weaken^ s (▶S∙ new) upA upB)
s2-weaken^ {k = k} (s-∀l {B = B} {A% = A%} grd regA s fd upC upD) new (↑ty-∀ upA) (↑ty-arr {A' = C'} {B' = D'} upB upB₁)
  with ⟨ B' , upB₂ ⟩ ← ↑ty-total B k
  with ⟨ C₁ , upC₁ ⟩ ← ↑ty0-total C'
  with ⟨ D₁ , upD₁ ⟩ ← ↑ty0-total D'
  with ⟨ A%' , upA% ⟩ ← ↑ty-total A% (#S k)
  = s-∀l (≫-weaken^ grd (▶S= new upB₂) upA upA%)
         (⊢r-weaken^ regA (▶S∙ new) upA)
         (s2-weaken^ s (▶S= new upB₂) upA% (↑ty-arr (↑ty-comm0' upB upC₁ upC) (↑ty-comm0' upB₁ upD₁ upD)))
         (↑ty-find0 fd upA) upC₁ upD₁
s2-weaken^ {k = k} (s-∀l-no-appear {A% = A%} grd regA s fd upC upD) new (↑ty-∀ upA) (↑ty-arr {A' = C'} {B' = D'} upB upB₁)
--  with ⟨ B' , upB₂ ⟩ ← ↑ty-total B k
  with ⟨ C₁ , upC₁ ⟩ ← ↑ty0-total C'
  with ⟨ D₁ , upD₁ ⟩ ← ↑ty0-total D'
  with ⟨ A%' , upA% ⟩ ← ↑ty-total A% (#S k)
  = s-∀l-no-appear (≫-weaken^ grd (▶S^ new) upA upA%)
         (⊢r-weaken^ regA (▶S∙ new) upA)
         (s2-weaken^ s (▶S^ new) upA% (↑ty-arr (↑ty-comm0' upB upC₁ upC) (↑ty-comm0' upB₁ upD₁ upD)))
         (¬ε-↑ty0' fd upA) upC₁ upD₁

s2-weaken^0 : Γ ⊢d² j # A ≤ B
            → ↑ty0 A ⇘ A'
            → ↑ty0 B ⇘ B'
            → Γ ,^ ⊢d² j # A' ≤ B'
s2-weaken^0 s upA upB = s2-weaken^ s ▶Z upA upB
