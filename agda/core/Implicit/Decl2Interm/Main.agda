module Implicit.Decl2Interm.Main where

open import Implicit.Language.All
open import Implicit.Decl.All renaming (_⊢_#_≤_ to _⊢d_#_≤_)
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

⊢d-refl-eq : Γ ⊢d ∞ # A ≤ B
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


≫-trans : SRegular Γ
        → Γ ≫ A ⇘ B
         → [ T / k ] Γ ∙⟹ Γ'
         → k ¬εᵍ Γ
         → Γ' ≫ B ⇘ C
         → Γ' ≫ A ⇘ C
≫-trans regΓ grd-int new nin grd-int = grd-int
≫-trans regΓ (grd-var= x) new nin grd2 with ⊢r-≫-eq' (∙⟹-⊢r (∋:=-⊢r regΓ x) new (εᵍ-:=-¬ε nin x)) grd2
... | refl = grd-var= (∙⟹-∋:=-prv x new)
≫-trans regΓ (grd-var∙ x) new nin (grd-var= x₁) = grd-var= x₁
≫-trans regΓ (grd-var∙ x) new nin (grd-var∙ x₁) = grd-var∙ x₁
≫-trans regΓ (grd-arr grd1 grd3) new nin (grd-arr grd2 grd4)
  = grd-arr (≫-trans regΓ grd1 new nin grd2) (≫-trans regΓ grd3 new nin grd4)
≫-trans {T = T} regΓ (grd-∀ grd1) new nin (grd-∀ grd2)
  with ⟨ T' , upT ⟩ ← ↑ty0-total T
  = grd-∀ (≫-trans (reg-S∙ regΓ) grd1 (∙⟹∙S new upT) (S∙ nin) grd2)

≫j-trans : SRegular Γ
         → Γ ≫ A ⇘ B by j
         → [ T / k ] Γ ∙⟹ Γ'
         → k ¬εᵍ Γ
         → Γ' ≫ B ⇘ C
         → Γ' ≫ A ⇘ C by j
≫j-trans regΓ (grd-Z x) new nin grd2 = grd-Z (≫-trans regΓ x new nin grd2)
≫j-trans regΓ (grd-∞ x) new nin grd2 = grd-∞ (≫-trans regΓ x new nin grd2)
≫j-trans regΓ (grd-arr-𝕚 x grd1) new nin (grd-arr grd2 grd3)
  = grd-arr-𝕚 (≫-trans regΓ x new nin grd2) (≫j-trans regΓ grd1 new nin grd3)
≫j-trans regΓ (grd-arr-𝕔 x grd1) new nin (grd-arr grd2 grd3)
  = grd-arr-𝕔 (≫-trans regΓ x new nin grd2) (≫j-trans regΓ grd1 new nin grd3)
≫j-trans {T = T} regΓ (grd-∀l-𝕚 grd1 upj) new nin (grd-∀ grd2)
  with ⟨ T' , upT ⟩ ← ↑ty0-total T
  = grd-∀l-𝕚 (≫j-trans (reg-S∙ regΓ) grd1 (∙⟹∙S new upT) (S∙ nin) grd2) upj
≫j-trans {T = T} regΓ (grd-∀l-𝕔 grd1 upj) new nin (grd-∀ grd2)
  with ⟨ T' , upT ⟩ ← ↑ty0-total T
  = grd-∀l-𝕔 (≫j-trans (reg-S∙ regΓ) grd1 (∙⟹∙S new upT) (S∙ nin) grd2) upj
≫j-trans {T = T} regΓ (grd-∀ grd1 upj) new nin (grd-∀ grd2)
  with ⟨ T' , upT ⟩ ← ↑ty0-total T
  = grd-∀ (≫j-trans (reg-S∙ regΓ) grd1 (∙⟹∙S new upT) (S∙ nin) grd2) upj

≫j-trans0 : SRegular Γ
          → Γ ⊢r B
          → Γ ,= B ≫ A₁ ⇘ A%
          → Γ ,∙ ≫ A ⇘ A₁ by j
          → Γ ,= B ≫ A ⇘ A% by j
≫j-trans0 {B = B} regΓ regB grd1 grd2
  with ⟨ B' , upB ⟩ ← ↑ty0-total B
  = ≫j-trans (reg-S∙ regΓ) grd2 (∙⟹^0 upB regB) Z∙ grd1

∋∙-∋:=-≢ : Γ ∋ X := A
         → Γ ∋∙ k
         → k ≢ X
∋∙-∋:=-≢ in1 in2 refl = ∋∙-∋:=-false in2 in1

¬ε-≫-∙ : k ¬ε A%
       → Γ ∋∙ k
       → k ¬εᵍ Γ
       → Γ ≫ A ⇘ A%
       → k ¬ε A
¬ε-≫-∙ ¬ε-int inΓ ninΓ grd-int = ¬ε-int
¬ε-≫-∙ (¬ε-var x) inΓ ninΓ (grd-var∙ x₁) = ¬ε-var x
¬ε-≫-∙ (¬ε-arr ninA ninA₁) inΓ ninΓ (grd-arr grd grd₁) = ¬ε-arr (¬ε-≫-∙ ninA inΓ ninΓ grd) (¬ε-≫-∙ ninA₁ inΓ ninΓ grd₁)
¬ε-≫-∙ ninA inΓ ninΓ (grd-var= x) = ¬ε-var (≢-sym (∋∙-∋:=-≢ x inΓ))
¬ε-≫-∙ (¬ε-∀ ninA) inΓ ninΓ (grd-∀ grd) = ¬ε-∀ (¬ε-≫-∙ ninA (S∙ inΓ) (S∙ ninΓ) grd)

ε-≫-∙ : k ε A%
      → Γ ∋∙ k
      → k ¬εᵍ Γ
      → Γ ≫ A ⇘ A%
      → k ε A
ε-≫-∙ ε-var inΓ ninΓ (grd-var= x) = ⊥-elim (εᵍ-:=-false x ε-var ninΓ)
ε-≫-∙ ε-var inΓ ninΓ (grd-var∙ x) = ε-var
ε-≫-∙ (ε-arr-l inA) inΓ ninΓ (grd-var= x) = ⊥-elim (εᵍ-:=-false x (ε-arr-l inA) ninΓ)
ε-≫-∙ (ε-arr-l inA) inΓ ninΓ (grd-arr grd grd₁) = ε-arr-l (ε-≫-∙ inA inΓ ninΓ grd)
ε-≫-∙ (ε-arr-r ¬inA inA) inΓ ninΓ (grd-var= x) = ⊥-elim (εᵍ-:=-false x (ε-arr-r ¬inA inA) ninΓ)
ε-≫-∙ (ε-arr-r ¬inA inA) inΓ ninΓ (grd-arr grd grd₁) = ε-arr-r (¬ε-≫-∙ ¬inA inΓ ninΓ grd) (ε-≫-∙ inA inΓ ninΓ grd₁)
ε-≫-∙ (ε-∀ inA) inΓ ninΓ (grd-var= x) = ⊥-elim (εᵍ-:=-false x (ε-∀ inA) ninΓ)
ε-≫-∙ (ε-∀ inA) inΓ ninΓ (grd-∀ grd) = ε-∀ (ε-≫-∙ inA (S∙ inΓ) (S∙ ninΓ) grd)



find-≫-∙ : find A% k j
         → k ¬εᵍ Γ
         → Γ ∋∙ k
         → Γ ≫ A ⇘ A% by j
         → find A k j
find-≫-∙ (f-∞ x) ninΓ inΓ (grd-∞ x₁) = f-∞ (ε-≫-∙ x inΓ ninΓ x₁)
find-≫-∙ (f-arr-𝕚-l x) ninΓ inΓ (grd-arr-𝕚 x₁ grd) = f-arr-𝕚-l (ε-≫-∙ x inΓ ninΓ x₁)
find-≫-∙ (f-arr-𝕚-r ¬inA fd) ninΓ inΓ (grd-arr-𝕚 x grd) = f-arr-𝕚-r (¬ε-≫-∙ ¬inA inΓ ninΓ x) (find-≫-∙ fd ninΓ inΓ grd)
find-≫-∙ (f-arr-𝕔 ¬inA fd) ninΓ inΓ (grd-arr-𝕔 x grd) = f-arr-𝕔 (¬ε-≫-∙ ¬inA inΓ ninΓ x) (find-≫-∙ fd ninΓ inΓ grd)
find-≫-∙ (f-∀-𝕚 fd upj) ninΓ inΓ (grd-∀l-𝕚 grd upj₁)
  with refl ← ↑tyʲ-unique upj upj₁
  = f-∀-𝕚 (find-≫-∙ fd (S∙ ninΓ) (S∙ inΓ) grd) upj
find-≫-∙ (f-∀-𝕔 fd upj) ninΓ inΓ (grd-∀l-𝕔 grd upj₁)
  with refl ← ↑tyʲ-unique upj upj₁
  = f-∀-𝕔 (find-≫-∙ fd (S∙ ninΓ) (S∙ inΓ) grd) upj
find-≫-∙ (f-𝕥 fd upj) ninΓ inΓ (grd-∀ grd upj₁)
  with refl ← ↑tyʲ-unique upj upj₁
  = f-𝕥 (find-≫-∙ fd (S∙ ninΓ) (S∙ inΓ) grd) upj



complete+ : Γ ⊢d j # A% ≤ B
--          → Γ ≫ A ⇘ A% by j
          → Γ ⊢i j # A ⌞ ≤⁺ ⌝ B

complete- : Γ ⊢d ∞ # A ≤ B%
          → Γ ≫ B ⇘ B%
          → Γ ⊢i ∞ # A ⌞ ≤⁻ ⌝ B

complete+ (s-refl regΔ cloA) (grd-Z x) = s-refl regΔ (⊢r-≫-⊢c x cloA) x
complete+ (s-int regΔ) (grd-∞ grd-int) = s-int regΔ
complete+ (s-int regΔ) (grd-∞ (grd-var= x)) = s-svar-l regΔ x
complete+ (s-var-∙ regΔ inΔ) (grd-∞ (grd-var= x)) = s-svar-l regΔ x
complete+ (s-var-∙ regΔ inΔ) (grd-∞ (grd-var∙ x)) = s-var-∙ regΔ x
complete+ (s-arr₁ s s₁) (grd-∞ (grd-var= x))
  with refl ← ⊢d-refl-eq s₁
  with refl ← ⊢d-refl-eq s = s-svar-l (s2-sregular s) x
complete+ (s-arr₁ s s₁) (grd-∞ (grd-arr x x₁)) = s-arr₁ (complete- s x) (complete+ s₁ (grd-∞ x₁))
complete+ (s-arr₂ s s₁) (grd-arr-𝕚 x grd) = s-arr₂ (complete- s x) (complete+ s₁ grd)
complete+ (s-arr₃ regA s) (grd-arr-𝕔 x grd) = s-arr₃ (⊢r-≫-⊢c x regA) x (complete+ s grd)
complete+ (s-∀ s) (grd-∞ (grd-var= x))
  with refl ← ⊢d-refl-eq s = s-svar-l (s2-sregular (s-∀ s)) x
complete+ (s-∀ s) (grd-∞ (grd-∀ x)) = s-∀ (complete+ s (grd-∞ x))
complete+ (s-∀l {B = B} grd₁ regA s case-𝕚 fd upC upD (↑tyʲ-𝕚 upj)) (grd-∀l-𝕚 grd upj₁)
  with refl ← ↑tyʲ-unique upj₁ upj
  with reg-S= regΓ regA ← s2-sregular s
  = s-∀l (complete+ s (≫j-trans0 regΓ regA grd₁ grd)) case-𝕚 (find-≫-∙ fd Z∙ Z grd) upC upD (↑tyʲ-𝕚 upj)
complete+ (s-∀l grd₁ regA s case-𝕔 fd upC upD (↑tyʲ-𝕔 upj)) (grd-∀l-𝕔 grd upj₁)
  with refl ← ↑tyʲ-unique upj₁ upj
  with reg-S= regΓ regA ← s2-sregular s
  = s-∀l (complete+ s (≫j-trans0 regΓ regA grd₁ grd)) case-𝕔 (find-≫-∙ fd Z∙ Z grd) upC upD (↑tyʲ-𝕔 upj)
complete+ (s-tapp {B = B} x regA' s upj) (grd-∀ grd upj')
  with refl ← ↑tyʲ-unique upj upj'
  with reg-S= regΓ regA ← s2-sregular s
  = s-tapp (complete+ s (≫j-trans0 regΓ regA x grd)) upj

complete- (s-int regΔ) grd-int = s-int regΔ
complete- (s-int regΔ) (grd-var= x) = s-svar-r regΔ x
complete- (s-var-∙ regΔ inΔ) (grd-var= x) = s-svar-r regΔ x
complete- (s-var-∙ regΔ inΔ) (grd-var∙ x) = s-var-∙ regΔ x
complete- (s-arr₁ s s₁) (grd-var= x)
  with refl ← ⊢d-refl-eq s₁
  with refl ← ⊢d-refl-eq s = s-svar-r (s2-sregular s) x
complete- (s-arr₁ s s₁) (grd-arr grd grd₁) = s-arr₁ (complete+ s (grd-∞ grd)) (complete- s₁ grd₁)
complete- (s-∀ s) (grd-var= x)
  with refl ← ⊢d-refl-eq s = s-svar-r (s2-sregular (s-∀ s)) x
complete- (s-∀ s) (grd-∀ grd) = s-∀ (complete- s grd)

complete0 : Γ ⊢d Z # A ≤ B
          → Γ ⊢i Z # A ⌞ ≤⁺ ⌝ B
complete0 (s-refl regΔ cloA) = complete+ (s-refl regΔ cloA) (grd-Z (⊢r-≫-eq cloA))

complete∞ : Γ ⊢d ∞ # A ≤ B
          → Γ ⊢i ∞ # A ⌞ ≤ ⌝ B
complete∞ {≤ = ≤⁺} s = complete+ s (grd-∞ (⊢r-≫-eq (s2-⊢r-l s)))
complete∞ {≤ = ≤⁻} s = complete- s (⊢r-≫-eq (s2-⊢r-r s))
