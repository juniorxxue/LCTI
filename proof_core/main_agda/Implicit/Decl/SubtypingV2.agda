module Implicit.Decl.SubtypingV2 where
-- small tweaks for better alignment with intermediate system

open import Implicit.Language.All

----------------------------------------------------------------------
--+                           Subtyping                            +--
----------------------------------------------------------------------

infix 3 _⊢d²_#_≤_
data _⊢d²_#_≤_ : Env n m → Counter m → Type m → Type m → Set where
  s-refl :
      (regΔ : SRegular Δ)
    → (cloA : Δ ⊢r A)
    → Δ ⊢d² Z # A ≤ A
  s-int :
      (regΔ : SRegular Δ)
    → Δ ⊢d² ∞ # Int ≤ Int
  s-var-∙ :
      (regΔ : SRegular Δ)
    → (inΔ : Δ ∋∙ X)
    → Δ ⊢d² ∞ # ‶ X ≤ ‶ X
  s-arr₁ :
      Δ ⊢d² ∞ # C ≤ A
    → Δ ⊢d² ∞ # B ≤ D
    → Δ ⊢d² ∞ # A `→ B ≤ C `→ D
  s-arr₂ :
      Δ ⊢d² ∞ # C ≤ A
    → Δ ⊢d² j # B ≤ D
    → Δ ⊢d² 𝕚 j # A `→ B ≤ C `→ D
  s-arr₃ :
      (regA : Δ ⊢r A)
    → Δ ⊢d² j # B ≤ D
    → Δ ⊢d² 𝕔 j # A `→ B ≤ A `→ D
  s-∀ :
      Δ ,∙ ⊢d² ∞ # A ≤ B
    → Δ ⊢d² ∞ # `∀ A ≤ `∀ B
  s-∀l :
      (grd : (Γ ,= B) ≫ A ⇘ A%)
    → (regA : Γ ,∙ ⊢r A)
    → Γ ,= B ⊢d² j' # A% ≤ C' `→ D'
    → (ic : (𝕚𝕔 j))
    → (fd : find A #0 j')
    → (upC : ↑ty0 C ⇘ C')
    → (upD : ↑ty0 D ⇘ D')
    → (upj : ↑tyʲ0 j ⇘ j')
    → Γ ⊢d² j # `∀ A ≤ C `→ D
  s-∀l-no-appear :
      (grd : (Γ ,^) ≫ A ⇘ A%)
    → (regA : Γ ,∙ ⊢r A)
    → Γ ,^ ⊢d² j' # A% ≤ C' `→ D'
    → (ic : (𝕚𝕔 j))
    → (fd : #0 ¬ε A)
    → (upC : ↑ty0 C ⇘ C')
    → (upD : ↑ty0 D ⇘ D')
    → (upj : ↑tyʲ0 j ⇘ j')
    → Γ ⊢d² j # `∀ A ≤ C `→ D
  s-tapp :
      (Δ ,= B) ≫ A ⇘ A%
    → (regA : Δ ,∙ ⊢r A)
    → Δ ,= B ⊢d² j' # A% ≤ C
    → (upj : ↑tyʲ0 j ⇘ j')
    → Δ ⊢d² 𝕥₍ B ₎ j # `∀ A ≤ `∀ C



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
s2-sregular (s-∀l grd regA s ic fd upC upD upj) with s2-sregular s
... | reg-S= r regA = r
s2-sregular (s-∀l-no-appear grd regA s ic fd upC upD upj) with s2-sregular s
... | reg-S^ r = r
s2-sregular (s-tapp x regA s upj) with s2-sregular s
... | reg-S= r regA = r


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
s2-⊢r-l (s-∀l grd regA s ic fd upC upD upj) = ⊢r-∀ regA
s2-⊢r-l (s-∀l-no-appear grd regA s ic fd upC upD upj) = ⊢r-∀ regA
s2-⊢r-l (s-tapp x regA s upj) = ⊢r-∀ regA

s2-⊢r-r (s-refl regΔ cloA) = cloA
s2-⊢r-r (s-int regΔ) = ⊢r-int
s2-⊢r-r (s-var-∙ regΔ inΔ) = ⊢r-var-∙ inΔ
s2-⊢r-r (s-arr₁ s s₁) = ⊢r-arr (s2-⊢r-l s) (s2-⊢r-r s₁)
s2-⊢r-r (s-arr₂ s s₁) = ⊢r-arr (s2-⊢r-l s) (s2-⊢r-r s₁)
s2-⊢r-r (s-arr₃ regA s) = ⊢r-arr regA (s2-⊢r-r s)
s2-⊢r-r (s-∀ s) = ⊢r-∀ (s2-⊢r-r s)
s2-⊢r-r (s-∀l grd regA s ic fd upC upD upj) = ⊢r-strengthen=0 (s2-⊢r-r s) (↑ty-arr upC upD)
s2-⊢r-r (s-∀l-no-appear grd regA s ic fd upC upD upj) = ⊢r-strengthen^0 (s2-⊢r-r s) (↑ty-arr upC upD)
s2-⊢r-r (s-tapp x regA s upj) = ⊢r-∀ (⊢r-◆0 (s2-⊢r-r s))

s2-weaken= : Γ ⊢d² j # A ≤ B
           → Γ ▶ k ,= T ⇘ Γ'
            → A ↑ty k ⇘ A'
            → B ↑ty k ⇘ B'
            → j ↑tyʲ k ⇘ j'
            → Γ' ⊢d² j' # A' ≤ B'
s2-weaken= (s-refl regΔ cloA) new upA upB ↑tyʲ-Z
  with refl ← ↑ty-unique upA upB = s-refl (sregular-weaken= regΔ new) (⊢r-weaken= cloA new upB)
s2-weaken= (s-int regΔ) new ↑ty-int ↑ty-int ↑tyʲ-∞ = s-int (sregular-weaken= regΔ new)
s2-weaken= (s-var-∙ regΔ inΔ) new ↑ty-var ↑ty-var ↑tyʲ-∞ = s-var-∙ (sregular-weaken= regΔ new) (∋∙-weaken= inΔ new)
s2-weaken= (s-arr₁ s s₁) new (↑ty-arr upA upA₁) (↑ty-arr upB upB₁) ↑tyʲ-∞ = s-arr₁ (s2-weaken= s new upB upA ↑tyʲ-∞) (s2-weaken= s₁ new upA₁ upB₁ ↑tyʲ-∞)
s2-weaken= (s-arr₂ s s₁) new (↑ty-arr upA upA₁) (↑ty-arr upB upB₁) (↑tyʲ-𝕚 upj)
  = s-arr₂ (s2-weaken= s new upB upA ↑tyʲ-∞) (s2-weaken= s₁ new upA₁ upB₁ upj)
s2-weaken= (s-arr₃ regA s) new (↑ty-arr upA upA₁) (↑ty-arr upB upB₁) (↑tyʲ-𝕔 upj)
  with refl ← ↑ty-unique upA upB = s-arr₃ (⊢r-weaken= regA new upB) (s2-weaken= s new upA₁ upB₁ upj)
s2-weaken= {T = T} (s-∀ s) new (↑ty-∀ upA) (↑ty-∀ upB) ↑tyʲ-∞
  with ⟨ T' , upT ⟩ ← ↑ty0-total T = s-∀ (s2-weaken= s (▶S∙ new upT) upA upB ↑tyʲ-∞)
s2-weaken= {k = k} {T = T} {j' = j'} (s-∀l {B = B} {A% = A%} grd regA s ic fd upC upD upj₁) new (↑ty-∀ upA) (↑ty-arr {A' = C'} {B' = D'} upB upB₁) upj
  with ⟨ T' , upT ⟩ ← ↑ty0-total T
  with ⟨ B' , upB₂ ⟩ ← ↑ty-total B k
  with ⟨ C₁ , upC₁ ⟩ ← ↑ty0-total C'
  with ⟨ D₁ , upD₁ ⟩ ← ↑ty0-total D'
  with ⟨ j₁ , upj₂ ⟩ ← ↑tyʲ0-total j'
  with ⟨ A%' , upA% ⟩ ← ↑ty-total A% (#S k)
  = s-∀l (≫-weaken= grd (▶S= new upT upB₂) upA upA%)
         (⊢r-weaken= regA (▶S∙ new upT) upA)
         (s2-weaken= s (▶S= new upT upB₂) upA% (↑ty-arr (↑ty-comm0' upB upC₁ upC) (↑ty-comm0' upB₁ upD₁ upD)) (↑tyʲ-comm0' upj upj₂ upj₁))
         (𝕚𝕔-↑tyʲ ic upj) (↑ty-find0 fd upA (↑tyʲ-comm0' upj upj₂ upj₁)) upC₁ upD₁ upj₂
s2-weaken= {k = k} {T = T} {j' = j'} (s-∀l-no-appear {A% = A%} grd regA s ic fd upC upD upj₁) new (↑ty-∀ upA) (↑ty-arr {A' = C'} {B' = D'} upB upB₁) upj
  with ⟨ T' , upT ⟩ ← ↑ty0-total T
--  with ⟨ B' , upB₂ ⟩ ← ↑ty-total B k
  with ⟨ C₁ , upC₁ ⟩ ← ↑ty0-total C'
  with ⟨ D₁ , upD₁ ⟩ ← ↑ty0-total D'
  with ⟨ j₁ , upj₂ ⟩ ← ↑tyʲ0-total j'
  with ⟨ A%' , upA% ⟩ ← ↑ty-total A% (#S k)
  = s-∀l-no-appear (≫-weaken= grd (▶S^ new upT) upA upA%)
         (⊢r-weaken= regA (▶S∙ new upT) upA)
         (s2-weaken= s (▶S^ new upT) upA% (↑ty-arr (↑ty-comm0' upB upC₁ upC) (↑ty-comm0' upB₁ upD₁ upD)) (↑tyʲ-comm0' upj upj₂ upj₁))
         (𝕚𝕔-↑tyʲ ic upj) (¬ε-↑ty0' fd upA) upC₁ upD₁ upj₂
s2-weaken= {k = k} {T = T}  {j' = 𝕥₍  _ ₎ j'} (s-tapp {B = B} {A% = A%} x regA s upj₁) new (↑ty-∀ upA) (↑ty-∀ upB) (↑tyʲ-𝕥 upj upA₁)
  with ⟨ j₁ , upj₂ ⟩ ← ↑tyʲ0-total j'
  with ⟨ T' , upT ⟩ ← ↑ty0-total T
  with ⟨ B' , upB₂ ⟩ ← ↑ty-total B k
  with ⟨ A%' , upA% ⟩ ← ↑ty-total A% (#S k)
  = s-tapp (≫-weaken= x (▶S= new upT upA₁) upA upA%)
           (⊢r-weaken= regA (▶S∙ new upT) upA)
           (s2-weaken= s (▶S= new upT upA₁) upA% upB (↑tyʲ-comm0' upj upj₂ upj₁)) upj₂


s2-weaken=0 : Γ ⊢d² j # A ≤ B
            → ↑ty0 A ⇘ A'
            → ↑ty0 B ⇘ B'
            → ↑tyʲ0 j ⇘ j'
            → Γ ⊢r T
            → Γ ,= T ⊢d² j' # A' ≤ B'
s2-weaken=0 s upA upB upj regT = s2-weaken= s (▶Z regT) upA upB upj


s2-weaken^ : Γ ⊢d² j # A ≤ B
           → Γ ▶ k ,^⇘ Γ'
            → A ↑ty k ⇘ A'
            → B ↑ty k ⇘ B'
            → j ↑tyʲ k ⇘ j'
            → Γ' ⊢d² j' # A' ≤ B'
s2-weaken^ (s-refl regΔ cloA) new upA upB ↑tyʲ-Z
  with refl ← ↑ty-unique upA upB = s-refl (sregular-weaken^ regΔ new) (⊢r-weaken^ cloA new upB)
s2-weaken^ (s-int regΔ) new ↑ty-int ↑ty-int ↑tyʲ-∞ = s-int (sregular-weaken^ regΔ new)
s2-weaken^ (s-var-∙ regΔ inΔ) new ↑ty-var ↑ty-var ↑tyʲ-∞ = s-var-∙ (sregular-weaken^ regΔ new) (∋∙-weaken^ inΔ new)
s2-weaken^ (s-arr₁ s s₁) new (↑ty-arr upA upA₁) (↑ty-arr upB upB₁) ↑tyʲ-∞ = s-arr₁ (s2-weaken^ s new upB upA ↑tyʲ-∞) (s2-weaken^ s₁ new upA₁ upB₁ ↑tyʲ-∞)
s2-weaken^ (s-arr₂ s s₁) new (↑ty-arr upA upA₁) (↑ty-arr upB upB₁) (↑tyʲ-𝕚 upj)
  = s-arr₂ (s2-weaken^ s new upB upA ↑tyʲ-∞) (s2-weaken^ s₁ new upA₁ upB₁ upj)
s2-weaken^ (s-arr₃ regA s) new (↑ty-arr upA upA₁) (↑ty-arr upB upB₁) (↑tyʲ-𝕔 upj)
  with refl ← ↑ty-unique upA upB = s-arr₃ (⊢r-weaken^ regA new upB) (s2-weaken^ s new upA₁ upB₁ upj)
s2-weaken^ (s-∀ s) new (↑ty-∀ upA) (↑ty-∀ upB) ↑tyʲ-∞ = s-∀ (s2-weaken^ s (▶S∙ new) upA upB ↑tyʲ-∞)
s2-weaken^ {k = k} {j' = j'} (s-∀l {B = B} {A% = A%} grd regA s ic fd upC upD upj₁) new (↑ty-∀ upA) (↑ty-arr {A' = C'} {B' = D'} upB upB₁) upj
  with ⟨ B' , upB₂ ⟩ ← ↑ty-total B k
  with ⟨ C₁ , upC₁ ⟩ ← ↑ty0-total C'
  with ⟨ D₁ , upD₁ ⟩ ← ↑ty0-total D'
  with ⟨ j₁ , upj₂ ⟩ ← ↑tyʲ0-total j'
  with ⟨ A%' , upA% ⟩ ← ↑ty-total A% (#S k)
  = s-∀l (≫-weaken^ grd (▶S= new upB₂) upA upA%)
         (⊢r-weaken^ regA (▶S∙ new) upA)
         (s2-weaken^ s (▶S= new upB₂) upA% (↑ty-arr (↑ty-comm0' upB upC₁ upC) (↑ty-comm0' upB₁ upD₁ upD)) (↑tyʲ-comm0' upj upj₂ upj₁))
         (𝕚𝕔-↑tyʲ ic upj) (↑ty-find0 fd upA (↑tyʲ-comm0' upj upj₂ upj₁)) upC₁ upD₁ upj₂
s2-weaken^ {k = k} {j' = j'} (s-∀l-no-appear {A% = A%} grd regA s ic fd upC upD upj₁) new (↑ty-∀ upA) (↑ty-arr {A' = C'} {B' = D'} upB upB₁) upj
--  with ⟨ B' , upB₂ ⟩ ← ↑ty-total B k
  with ⟨ C₁ , upC₁ ⟩ ← ↑ty0-total C'
  with ⟨ D₁ , upD₁ ⟩ ← ↑ty0-total D'
  with ⟨ j₁ , upj₂ ⟩ ← ↑tyʲ0-total j'
  with ⟨ A%' , upA% ⟩ ← ↑ty-total A% (#S k)
  = s-∀l-no-appear (≫-weaken^ grd (▶S^ new) upA upA%)
         (⊢r-weaken^ regA (▶S∙ new) upA)
         (s2-weaken^ s (▶S^ new) upA% (↑ty-arr (↑ty-comm0' upB upC₁ upC) (↑ty-comm0' upB₁ upD₁ upD)) (↑tyʲ-comm0' upj upj₂ upj₁))
         (𝕚𝕔-↑tyʲ ic upj) (¬ε-↑ty0' fd upA) upC₁ upD₁ upj₂
s2-weaken^ {k = k} {j' = 𝕥₍  _ ₎ j'} (s-tapp {B = B} {A% = A%} x regA s upj₁) new (↑ty-∀ upA) (↑ty-∀ upB) (↑tyʲ-𝕥 upj upA₁)
  with ⟨ j₁ , upj₂ ⟩ ← ↑tyʲ0-total j'
  with ⟨ B' , upB₂ ⟩ ← ↑ty-total B k
  with ⟨ A%' , upA% ⟩ ← ↑ty-total A% (#S k)
  = s-tapp (≫-weaken^ x (▶S= new upA₁) upA upA%)
           (⊢r-weaken^ regA (▶S∙ new) upA)
           (s2-weaken^ s (▶S= new upA₁) upA% upB (↑tyʲ-comm0' upj upj₂ upj₁)) upj₂

s2-weaken^0 : Γ ⊢d² j # A ≤ B
            → ↑ty0 A ⇘ A'
            → ↑ty0 B ⇘ B'
            → ↑tyʲ0 j ⇘ j'
            → Γ ,^ ⊢d² j' # A' ≤ B'
s2-weaken^0 s upA upB upj = s2-weaken^ s ▶Z upA upB upj
