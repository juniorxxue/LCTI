module Implicit.Decl2Interm.Main where

open import Implicit.Language.All
open import Implicit.Decl.All renaming (_⊢_#_⌞_⌝_ to _⊢d_#_⌞_⌝_)
open import Implicit.Interm.All renaming (_⊢_#_⌞_⌝_ to _⊢i_#_⌞_⌝_)

infix 3 _≫_⇘_by_
data _≫_⇘_by_ : Env n m → Type m → Type m → Counter m → Set
data _≫_⇘_by_ where
  grd-Z : Δ ≫ A ⇘ A%
           → Δ ≫ A ⇘ A% by Z
  grd-∞ : Δ ≫ A ⇘ A%
           → Δ ≫ A ⇘ A% by ∞
  grd-arr-𝕚 : Δ ≫ A ⇘ A%
            → Δ ≫ B ⇘ B% by j
            → Δ ≫ (A `→ B) ⇘ A% `→ B% by (𝕚 j)
  grd-arr-𝕔 : Δ ≫ A ⇘ A%
            → Δ ≫ B ⇘ B% by j
            → Δ ≫ (A `→ B) ⇘ A% `→ B% by (𝕔 j)
  grd-∀l-𝕚 : Δ ,∙ ≫ A ⇘ A% by (𝕚 j')
             → (upj : ↑tyʲ0 j ⇘ j')
            →  Δ ≫ `∀ A ⇘ `∀ A% by (𝕚 j)
  grd-∀l-𝕔 : Δ ,∙ ≫ A ⇘ A% by (𝕔 j')
           → (upj : ↑tyʲ0 j ⇘ j')
           → Δ ≫ `∀ A ⇘ `∀ A% by (𝕔 j)
  grd-∀   : Δ ,∙ ≫ A ⇘ A% by j'
          → (upj : ↑tyʲ0 j ⇘ j')
          → Δ ≫ `∀ A ⇘ `∀ A% by 𝕥₍ B ₎ j

⊢d-refl-eq : Γ ⊢d ∞ # A ⌞ ≤ ⌝ B
           → A ≡ B
⊢d-refl-eq (s-int regΔ) = refl
⊢d-refl-eq (s-var-∙ regΔ inΔ) = refl
⊢d-refl-eq (s-arr₁ s s₁) = cong₂ _`→_ (sym (⊢d-refl-eq s)) (⊢d-refl-eq s₁)
⊢d-refl-eq (s-∀ s) = cong `∀_ (⊢d-refl-eq s)

⊢r-≫-⊢c : Γ ≫ A ⇘ A%
        → Γ ⊢r A%
        → Γ ⊢c A
⊢r-≫-⊢c grd-int regA = ⊢c-int
⊢r-≫-⊢c (grd-var= x) regA = ⊢c-var-= (∋:=to∋= x)
⊢r-≫-⊢c (grd-var∙ x) regA = ⊢c-var-∙ x
⊢r-≫-⊢c (grd-arr grd grd₁) (⊢r-arr regA regA₁) = ⊢c-arr (⊢r-≫-⊢c grd regA) (⊢r-≫-⊢c grd₁ regA₁)
⊢r-≫-⊢c (grd-∀ grd) (⊢r-∀ regA) = ⊢c-∀ (⊢r-≫-⊢c grd regA)


postulate
  sd-sregular : Γ ⊢d j # A ⌞ ≤ ⌝ B
              → SRegular Γ
  sd-⊢r-l : Γ ⊢d j # A ⌞ ≤ ⌝ B
          → Γ ⊢r A
  sd-⊢r-r : Γ ⊢d j # A ⌞ ≤ ⌝ B
          → Γ ⊢r B


-- replace entry a with a solution ^a=A in an environment
infix 3 [_/_]_∙⟹_
data [_/_]_∙⟹_ : Type m → Fin m → Env n m → Env n m → Set where
  ∙⟹^0 : (up : ↑ty0 A ⇘ A')
        → [ A' / #0 ] (Γ ,∙) ∙⟹ (Γ ,= A)

  ∙⟹^S : [ A / k ] Γ ∙⟹ Γ'
        → (up1 : ↑ty0 A ⇘ A')
        → [ A' / #S k ] (Γ ,^) ∙⟹ Γ' ,^

  ∙⟹∙S : [ A / k ] Γ ∙⟹ Γ'
        → (up1 : ↑ty0 A ⇘ A')
        → [ A' / #S k ] (Γ ,∙) ∙⟹ (Γ' ,∙)

  ∙⟹,S : [ A / k ] Γ ∙⟹ Γ'
       → [ A / k ] (Γ , B) ∙⟹ (Γ' , B)

  ∙⟹=S : [ A / k ] Γ ∙⟹ Γ'
        → (up1 : ↑ty0 A ⇘ A')
        → [ A' / #S k ] (Γ ,= B) ∙⟹ (Γ' ,= B)


≫-trans : Γ ≫ A ⇘ B
         → [ T / k ] Γ ∙⟹ Γ'
          → Γ' ≫ B ⇘ C
          → Γ' ≫ A ⇘ C
≫-trans grd-int new grd-int = grd-int
≫-trans (grd-var= x) new grd2 = grd-var= {!!}
≫-trans (grd-var∙ x) new grd2 = grd2
≫-trans (grd-arr grd1 grd3) new (grd-arr grd2 grd4) = grd-arr (≫-trans grd1 new grd2) (≫-trans grd3 new grd4)
≫-trans {T = T} (grd-∀ grd1) new (grd-∀ grd2)
  with ⟨ T' , upT ⟩ ← ↑ty0-total T = grd-∀ (≫-trans grd1 (∙⟹∙S new upT) grd2)


≫j-trans : Γ ≫ A ⇘ B by j
         → [ T / k ] Γ ∙⟹ Γ'
          → Γ' ≫ B ⇘ C
          → Γ' ≫ A ⇘ C by j
≫j-trans (grd-Z x) new grd2 = grd-Z (≫-trans x new grd2)
≫j-trans (grd-∞ x) new grd2 = grd-∞ (≫-trans x new grd2)
≫j-trans (grd-arr-𝕚 x grd1) new (grd-arr grd2 grd3) = grd-arr-𝕚 (≫-trans x new grd2) (≫j-trans grd1 new grd3)
≫j-trans (grd-arr-𝕔 x grd1) new (grd-arr grd2 grd3) = grd-arr-𝕔 (≫-trans x new grd2) (≫j-trans grd1 new grd3)
≫j-trans {T = T} (grd-∀l-𝕚 grd1 upj) new (grd-∀ grd2)
  with ⟨ T' , upT ⟩ ← ↑ty0-total T = grd-∀l-𝕚 (≫j-trans grd1 (∙⟹∙S new upT) grd2) upj
≫j-trans {T = T} (grd-∀l-𝕔 grd1 upj) new (grd-∀ grd2)
  with ⟨ T' , upT ⟩ ← ↑ty0-total T = grd-∀l-𝕔 (≫j-trans grd1 (∙⟹∙S new upT) grd2) upj
≫j-trans {T = T} (grd-∀ grd1 upj) new (grd-∀ grd2)
  with ⟨ T' , upT ⟩ ← ↑ty0-total T = grd-∀ (≫j-trans grd1 (∙⟹∙S new upT) grd2) upj

complete+ : Γ ⊢d j # A% ⌞ ≤⁺ ⌝ B
          → Γ ≫ A ⇘ A% by j
          → Γ ⊢i j # A ⌞ ≤⁺ ⌝ B

complete- : Γ ⊢d ∞ # A ⌞ ≤⁻ ⌝ B%
          → Γ ≫ B ⇘ B%
          → Γ ⊢i ∞ # A ⌞ ≤⁻ ⌝ B

complete+ (s-refl regΔ cloA) (grd-Z x) = s-refl regΔ (⊢r-≫-⊢c x cloA) x
complete+ (s-int regΔ) (grd-∞ grd-int) = s-int regΔ
complete+ (s-int regΔ) (grd-∞ (grd-var= x)) = s-svar-l regΔ x
complete+ (s-var-∙ regΔ inΔ) (grd-∞ (grd-var= x)) = s-svar-l regΔ x
complete+ (s-var-∙ regΔ inΔ) (grd-∞ (grd-var∙ x)) = s-var-∙ regΔ x
complete+ (s-arr₁ s s₁) (grd-∞ (grd-var= x))
  with refl ← ⊢d-refl-eq s₁
  with refl ← ⊢d-refl-eq s = s-svar-l (sd-sregular s) x
complete+ (s-arr₁ s s₁) (grd-∞ (grd-arr x x₁)) = s-arr₁ (complete- s x) (complete+ s₁ (grd-∞ x₁))
complete+ (s-arr₂ s s₁) (grd-arr-𝕚 x grd) = s-arr₂ (complete- s x) (complete+ s₁ grd)
complete+ (s-arr₃ regA s) (grd-arr-𝕔 x grd) = s-arr₃ (⊢r-≫-⊢c x regA) x (complete+ s grd)
complete+ (s-∀ s) (grd-∞ (grd-var= x))
  with refl ← ⊢d-refl-eq s = s-svar-l (sd-sregular (s-∀ s)) x
complete+ (s-∀ s) (grd-∞ (grd-∀ x)) = s-∀ (complete+ s (grd-∞ x))
complete+ (s-∀l {B = B} grd₁ s case-𝕚 fd upC upD (↑tyʲ-𝕚 upj)) (grd-∀l-𝕚 grd upj₁)
  with refl ← ↑tyʲ-unique upj₁ upj
  = s-∀l (complete+ s (≫j-trans grd (∙⟹^0 (proj₂ (↑ty0-total B))) grd₁)) case-𝕚 {!!} upC upD (↑tyʲ-𝕚 upj)
complete+ (s-∀l grd₁ s ic fd upC upD upj) (grd-∀l-𝕔 grd upj₁) = {!!}
complete+ (s-tapp {B = B} x s upC upj) (grd-∀ grd upj₁)
  with refl ← ↑tyʲ-unique upj upj₁ = s-tapp (complete+ s (≫j-trans grd (∙⟹^0 (proj₂ (↑ty0-total B))) x)) upj

complete- (s-int regΔ) grd-int = s-int regΔ
complete- (s-int regΔ) (grd-var= x) = s-svar-r regΔ x
complete- (s-var-∙ regΔ inΔ) (grd-var= x) = s-svar-r regΔ x
complete- (s-var-∙ regΔ inΔ) (grd-var∙ x) = s-var-∙ regΔ x
complete- (s-arr₁ s s₁) (grd-var= x)
  with refl ← ⊢d-refl-eq s₁
  with refl ← ⊢d-refl-eq s = s-svar-r (sd-sregular s) x
complete- (s-arr₁ s s₁) (grd-arr grd grd₁) = s-arr₁ (complete+ s (grd-∞ grd)) (complete- s₁ grd₁)
complete- (s-∀ s) (grd-var= x)
  with refl ← ⊢d-refl-eq s = s-svar-r (sd-sregular (s-∀ s)) x
complete- (s-∀ s) (grd-∀ grd) = s-∀ (complete- s grd)

complete0 : Γ ⊢d Z # A ⌞ ≤ ⌝ B
          → Γ ⊢i Z # A ⌞ ≤ ⌝ B
complete0 (s-refl regΔ cloA) = complete+ (s-refl regΔ cloA) (grd-Z (⊢r-≫-eq cloA))

complete∞ : Γ ⊢d ∞ # A ⌞ ≤ ⌝ B
          → Γ ⊢i ∞ # A ⌞ ≤ ⌝ B
complete∞ {≤ = ≤⁺} s = complete+ s (grd-∞ (⊢r-≫-eq (sd-⊢r-l s)))
complete∞ {≤ = ≤⁻} s = complete- s (⊢r-≫-eq (sd-⊢r-r s))
