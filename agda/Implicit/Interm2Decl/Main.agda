module Implicit.Interm2Decl.Main where

open import Implicit.Language.All
open import Implicit.Decl.All renaming (_⊢_#_≤_ to _⊢d_#_≤_)
open import Implicit.Interm.All renaming (_⊢_#_⌞_⌝_ to _⊢i_#_⌞_⌝_)

postulate

  sd-strengthen=0 : Γ ,= T ⊢d j' # A' ≤ B'
                  → ↑ty0 A ⇘ A'
                  → ↑ty0 B ⇘ B'
                  → ↑tyʲ0 j ⇘ j'
                  → Γ ⊢d j # A ≤ B


sd-refl-∞ : SRegular Γ
          → Γ ⊢r A
          → Γ ⊢d ∞ # A ≤ A
sd-refl-∞ regΓ ⊢r-int = s-int regΓ
sd-refl-∞ regΓ (⊢r-var-∙ inΓ) = s-var-∙ regΓ inΓ
sd-refl-∞ regΓ (⊢r-arr regA regA₁) = s-arr₁ (sd-refl-∞ regΓ regA) (sd-refl-∞ regΓ regA₁)
sd-refl-∞ regΓ (⊢r-∀ regA) = s-∀ (sd-refl-∞ (reg-S∙ regΓ) regA)


≫-unique : Γ ≫ A ⇘ A₁
         → Γ ≫ A ⇘ A₂
         → A₁ ≡ A₂
≫-unique grd-int grd-int = refl
≫-unique (grd-var= x) (grd-var= x₁) = ∋:=-unique x x₁
≫-unique (grd-var= x) (grd-var∙ x₁) = ⊥-elim (∋∙-∋:=-false x₁ x)
≫-unique (grd-var∙ x) (grd-var= x₁) = ⊥-elim (∋∙-∋:=-false x x₁)
≫-unique (grd-var∙ x) (grd-var∙ x₁) = refl
≫-unique (grd-arr grd1 grd3) (grd-arr grd2 grd4) = cong₂ _`→_ (≫-unique grd1 grd2) (≫-unique grd3 grd4)
≫-unique (grd-∀ grd1) (grd-∀ grd2) = cong `∀_ (≫-unique grd1 grd2)

≫-trans : SRegular Γ
        → Γ ≫ A ⇘ B
         → [ T / k ] Γ ∙⟹ Γ'
         → k ¬εᵍ Γ
         → Γ' ≫ A ⇘ C
         → Γ' ≫ B ⇘ C
≫-trans regΓ grd-int new ninΓ grd-int = grd-int
≫-trans regΓ (grd-var= x) new ninΓ (grd-var= x₁)
  with refl ← ∙⟹-:=-eq x new x₁ = ⊢r-≫-eq (∙⟹-⊢r (∋:=-⊢r regΓ x) new (εᵍ-:=-¬ε ninΓ x))
≫-trans regΓ (grd-var= x) new ninΓ (grd-var∙ x₁) = ⊥-elim (∙⟹-:=-∙-false x new x₁)
≫-trans regΓ (grd-var∙ x) new ninΓ (grd-var= x₁) = grd-var= x₁
≫-trans regΓ (grd-var∙ x) new ninΓ (grd-var∙ x₁) = grd-var∙ x₁
≫-trans regΓ (grd-arr grd1 grd3) new ninΓ (grd-arr grd2 grd4) = grd-arr (≫-trans regΓ grd1 new ninΓ grd2)
                                                                        (≫-trans regΓ grd3 new ninΓ grd4)
≫-trans {T = T} regΓ (grd-∀ grd1) new ninΓ (grd-∀ grd2) = grd-∀ (≫-trans (reg-S∙ regΓ) grd1 (∙⟹∙S new (proj₂ (↑ty0-total T))) (S∙ ninΓ) grd2)


≫-total : SRegular Γ
        → Γ ⊢c A
        → ∃[ A% ](Γ ≫ A ⇘ A%)
≫-total regΓ ⊢c-int = ⟨ Int , grd-int ⟩
≫-total regΓ (⊢c-var-∙ {X = X} inΔ) = ⟨ ‶ X , grd-var∙ inΔ ⟩
≫-total regΓ (⊢c-var-= inΔ) with ∋:=-total inΔ
... | ⟨ A' , in1 ⟩ = ⟨ A' , grd-var= in1 ⟩
≫-total regΓ (⊢c-arr cloA cloA₁) = ⟨ ≫-total regΓ cloA .proj₁ `→ ≫-total regΓ cloA₁ .proj₁ ,
                                    grd-arr (≫-total regΓ cloA .proj₂) (≫-total regΓ cloA₁ .proj₂) ⟩
≫-total regΓ (⊢c-∀ cloA) = ⟨ `∀ ≫-total (reg-S∙ regΓ) cloA .proj₁ ,
                            grd-∀ (≫-total (reg-S∙ regΓ) cloA .proj₂) ⟩


¬ε-≫-∙ : k ¬ε A
       → Γ ∋∙ k
       → k ¬εᵍ Γ
       → Γ ≫ A ⇘ A%
       → k ¬ε A%
¬ε-≫-∙ ¬ε-int inΓ ninΓ grd-int = ¬ε-int
¬ε-≫-∙ (¬ε-var x) inΓ ninΓ (grd-var= x₁) = εᵍ-:=-¬ε ninΓ x₁
¬ε-≫-∙ (¬ε-var x) inΓ ninΓ (grd-var∙ x₁) = ¬ε-var x
¬ε-≫-∙ (¬ε-arr ninA ninA₁) inΓ ninΓ (grd-arr grd grd₁) = ¬ε-arr (¬ε-≫-∙ ninA inΓ ninΓ grd) (¬ε-≫-∙ ninA₁ inΓ ninΓ grd₁)
¬ε-≫-∙ (¬ε-∀ ninA) inΓ ninΓ (grd-∀ grd) = ¬ε-∀ (¬ε-≫-∙ ninA (S∙ inΓ) (S∙ ninΓ) grd)

ε-≫-∙ : k ε A
      → Γ ∋∙ k
      → k ¬εᵍ Γ
      → Γ ≫ A ⇘ A%
      → k ε A%
ε-≫-∙ ε-var inΓ ninΓ (grd-var= x) = ⊥-elim (∋∙-∋:=-false inΓ x)
ε-≫-∙ ε-var inΓ ninΓ (grd-var∙ x) = ε-var
ε-≫-∙ (ε-arr-l inA) inΓ ninΓ (grd-arr grd grd₁) = ε-arr-l (ε-≫-∙ inA inΓ ninΓ grd)
ε-≫-∙ (ε-arr-r ¬inA inA) inΓ ninΓ (grd-arr grd grd₁) = ε-arr-r (¬ε-≫-∙ ¬inA inΓ ninΓ grd) (ε-≫-∙ inA inΓ ninΓ grd₁)
ε-≫-∙ (ε-∀ inA) inΓ ninΓ (grd-∀ grd) = ε-∀ (ε-≫-∙ inA (S∙ inΓ) (S∙ ninΓ) grd)

find-≫-∙ : find A k j
         → k ¬εᵍ Γ
         → Γ ∋∙ k
         → Γ ≫ A ⇘ A%
         → find A% k j
find-≫-∙ (f-∞ x) ninΓ inΓ grd = f-∞ (ε-≫-∙ x inΓ ninΓ grd)
find-≫-∙ (f-arr-𝕚-l x) ninΓ inΓ (grd-arr grd grd₁) = f-arr-𝕚-l (ε-≫-∙ x inΓ ninΓ grd)
find-≫-∙ (f-arr-𝕚-r ¬inA fd) ninΓ inΓ (grd-arr grd grd₁) = f-arr-𝕚-r (¬ε-≫-∙ ¬inA inΓ ninΓ grd) (find-≫-∙ fd ninΓ inΓ grd₁)
find-≫-∙ (f-arr-𝕔 ¬inA fd) ninΓ inΓ (grd-arr grd grd₁) = f-arr-𝕔 (¬ε-≫-∙ ¬inA inΓ ninΓ grd) (find-≫-∙ fd ninΓ inΓ grd₁)
find-≫-∙ (f-∀-𝕚 fd upj) ninΓ inΓ (grd-∀ grd) = f-∀-𝕚 (find-≫-∙ fd (S∙ ninΓ) (S∙ inΓ) grd) upj
find-≫-∙ (f-∀-𝕔 fd upj) ninΓ inΓ (grd-∀ grd) = f-∀-𝕔 (find-≫-∙ fd (S∙ ninΓ) (S∙ inΓ) grd) upj
find-≫-∙ (f-𝕥 fd upj) ninΓ inΓ (grd-∀ grd) = f-𝕥 (find-≫-∙ fd (S∙ ninΓ) (S∙ inΓ) grd) upj


sound : Γ ⊢i j # A ⌞ ≤ ⌝ B
      → Γ ≫ A ⇘ A%
      → Γ ≫ B ⇘ B%
      → Γ ⊢d j # A% ≤ B%
sound (s-refl regΔ cloA grd) grd1 grd2
  with refl ← ≫-unique grd1 grd
  with refl ← ⊢r-≫-eq' (⊢c-≫-⊢r regΔ cloA grd1) grd2 = s-refl regΔ (⊢c-≫-⊢r regΔ cloA grd)
sound (s-int regΔ) grd-int grd-int = s-int regΔ
sound (s-var-∙ regΔ inΔ) (grd-var= x) (grd-var= x₁) = ⊥-elim (∋∙-∋:=-false inΔ x₁)
sound (s-var-∙ regΔ inΔ) (grd-var= x) (grd-var∙ x₁) = ⊥-elim (∋∙-∋:=-false inΔ x)
sound (s-var-∙ regΔ inΔ) (grd-var∙ x) (grd-var= x₁) = ⊥-elim (∋∙-∋:=-false inΔ x₁)
sound (s-var-∙ regΔ inΔ) (grd-var∙ x) (grd-var∙ x₁) = s-var-∙ regΔ x₁
sound (s-arr₁ s s₁) (grd-arr grd1 grd3) (grd-arr grd2 grd4) = s-arr₁ (sound s grd2 grd1) (sound s₁ grd3 grd4)
sound (s-arr₂ s s₁) (grd-arr grd1 grd3) (grd-arr grd2 grd4) = s-arr₂ (sound s grd2 grd1) (sound s₁ grd3 grd4)
sound (s-arr₃ cloA grd s) (grd-arr grd1 grd3) (grd-arr grd2 grd4)
  with refl ← ≫-unique grd grd1
  with regA ← ⊢c-≫-⊢r (s-sregular s) cloA grd
  with refl ← ⊢r-≫-eq' regA grd2 = s-arr₃ regA (sound s grd3 grd4)
sound (s-∀ s) (grd-∀ grd1) (grd-∀ grd2) = s-∀ (sound s grd1 grd2)
sound s'@(s-∀l {B = B} s ic fd upC upD upj) (grd-∀ grd1) grdCD@(grd-arr grd2 grd3)
  with cloA ← s-⊢c-l s
  with ⟨ A% , grdA ⟩ ← ≫-total (s-sregular s) cloA
  with reg-S= regΓ regA ← s-sregular s
  with regCD ← s+-polarity s'
  with refl ← ⊢r-≫-eq' regCD grdCD
  = s-∀l (≫-trans (reg-S∙ regΓ) grd1 (∙⟹^0 (proj₂ (↑ty0-total B)) regA) Z∙ grdA)
         (⊢c-≫-⊢r (reg-S∙ regΓ) (⊢c-◆0 (s-⊢c-l s)) grd1)
         (sound s grdA (⊢r-≫-eq (s+-polarity s)))
         ic
         (find-≫-∙ fd Z∙ Z grd1)
         upC
         upD
         upj
sound (s-tapp {B = B} s upj) (grd-∀ grd1) (grd-∀ grd2)
  with cloA ← s-⊢c-l s
  with ⟨ A% , grdA ⟩ ← ≫-total (s-sregular s) cloA
  with reg-S= regΓ regA ← s-sregular s
  with refl ← ⊢r-≫-eq' (⊢r-◆0 (s+-polarity s)) grd2
  = s-tapp (≫-trans (reg-S∙ regΓ) grd1 (∙⟹^0 (proj₂ (↑ty0-total B)) regA) Z∙ grdA)
           (⊢c-≫-⊢r (reg-S∙ regΓ) (⊢c-◆0 cloA) grd1)
           (sound s grdA (⊢r-≫-eq (s+-polarity s))) upj
sound (s-svar-l x inΔ) (grd-var= x₁) grd2
  with refl ← ∋:=-unique inΔ x₁
  with regA ← ∋:=-⊢r x inΔ
  with refl ← ⊢r-≫-eq' regA grd2
  = sd-refl-∞ x regA
sound (s-svar-l x inΔ) (grd-var∙ x₁) grd2 = ⊥-elim (∋∙-∋:=-false x₁ inΔ)
sound (s-svar-r x inΔ) grd1 (grd-var= x₁)
  with refl ← ∋:=-unique inΔ x₁
  with regA ← ∋:=-⊢r x inΔ
  with refl ← ⊢r-≫-eq' regA grd1 = sd-refl-∞ x regA
sound (s-svar-r x inΔ) grd1 (grd-var∙ x₁) = ⊥-elim (∋∙-∋:=-false x₁ inΔ)
