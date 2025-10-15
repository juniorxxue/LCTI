module Implicit.Language.Ground.Properties where

open import Implicit.Language.Base
open import Implicit.Language.Shift.All
open import Implicit.Language.Lookup.All
open import Implicit.Language.Occur.All
open import Implicit.Language.OpenClose.Base
open import Implicit.Language.Regular.All
open import Implicit.Language.Ground.Base
open import Implicit.Language.Extension.All
open import Implicit.Language.EnvOps.All
open import Implicit.Language.Find.All

⊢c-≫-⊢r : SRegular Γ
          → Γ ⊢c A
          → Γ ≫ A ⇘ A%
          → Γ ⊢r A%
⊢c-≫-⊢r regΓ ⊢c-int grd-int = ⊢r-int
⊢c-≫-⊢r regΓ (⊢c-var-∙ inΔ) (grd-var= x) = ⊥-elim (∋∙-∋:=-false inΔ x)
⊢c-≫-⊢r regΓ (⊢c-var-∙ inΔ) (grd-var∙ x) = ⊢r-var-∙ inΔ
⊢c-≫-⊢r regΓ (⊢c-var-= inΔ) (grd-var= x) = ∋:=-⊢r regΓ x
⊢c-≫-⊢r regΓ (⊢c-var-= inΔ) (grd-var∙ x) = ⊥-elim (∋∙-∋=-false x inΔ)
⊢c-≫-⊢r regΓ (⊢c-arr cloA cloA₁) (grd-arr grd grd₁) = ⊢r-arr (⊢c-≫-⊢r regΓ cloA grd) (⊢c-≫-⊢r regΓ cloA₁ grd₁)
⊢c-≫-⊢r regΓ (⊢c-∀ cloA) (grd-∀ grd) = ⊢r-∀ (⊢c-≫-⊢r (reg-S∙ regΓ) cloA grd)

⊢r-≫-⊢c : Γ ≫ A ⇘ A%
        → Γ ⊢r A%
        → Γ ⊢c A
⊢r-≫-⊢c grd-int regA = ⊢c-int
⊢r-≫-⊢c (grd-var= x) regA = ⊢c-var-= (∋:=to∋= x)
⊢r-≫-⊢c (grd-var∙ x) regA = ⊢c-var-∙ x
⊢r-≫-⊢c (grd-arr grd grd₁) (⊢r-arr regA regA₁) = ⊢c-arr (⊢r-≫-⊢c grd regA) (⊢r-≫-⊢c grd₁ regA₁)
⊢r-≫-⊢c (grd-∀ grd) (⊢r-∀ regA) = ⊢c-∀ (⊢r-≫-⊢c grd regA)


⊢r-≫-eq : Γ ⊢r A
        → Γ ≫ A ⇘ A
⊢r-≫-eq ⊢r-int = grd-int
⊢r-≫-eq (⊢r-var-∙ inΓ) = grd-var∙ inΓ
⊢r-≫-eq (⊢r-arr regA regA₁) = grd-arr (⊢r-≫-eq regA) (⊢r-≫-eq regA₁)
⊢r-≫-eq (⊢r-∀ regA) = grd-∀ (⊢r-≫-eq regA)

⊢r-≫-eq' : Γ ⊢r A
         → Γ ≫ A ⇘ A%
         → A ≡ A%
⊢r-≫-eq' ⊢r-int grd-int = refl
⊢r-≫-eq' (⊢r-var-∙ inΓ) (grd-var= x) = ⊥-elim (∋∙-∋:=-false inΓ x)
⊢r-≫-eq' (⊢r-var-∙ inΓ) (grd-var∙ x) = refl
⊢r-≫-eq' (⊢r-arr regA regA₁) (grd-arr grd grd₁) = cong₂ _`→_ (⊢r-≫-eq' regA grd) (⊢r-≫-eq' regA₁ grd₁)
⊢r-≫-eq' (⊢r-∀ regA) (grd-∀ grd) = cong `∀_ (⊢r-≫-eq' regA grd)

⊢c-≫-⊢c : SRegular Γ
          → Γ ⊢c A
          → Γ ≫ A ⇘ A%
          → Γ ⊢c A%
⊢c-≫-⊢c regΓ cloA grd = ⊢r-⊢c (⊢c-≫-⊢r regΓ cloA grd)


⊆-⊢c-≫ : Γ ⊆ Δ
       → Γ ⊢c A
       → Δ ≫ A ⇘ A%
       → Γ ≫ A ⇘ A%
⊆-⊢c-≫ ext ⊢c-int grd-int = grd-int
⊆-⊢c-≫ ext (⊢c-var-∙ inΔ) (grd-var= x) = ⊥-elim (∋∙-∋:=-false (⊆-∋∙ inΔ ext) x)
⊆-⊢c-≫ ext (⊢c-var-∙ inΔ) (grd-var∙ x) = grd-var∙ inΔ
⊆-⊢c-≫ ext (⊢c-var-= inΔ) (grd-var= x) = grd-var= (helper x ext inΔ)
  where helper : Δ ∋ X := A%
               → Γ ⊆ Δ
               → Γ ∋= X
               → Γ ∋ X := A%
        helper (Z up) (svar ext regA) Z = Z up
        helper (S∙ inΔ up) (uvar ext) (S∙ inΓ) = S∙ (helper inΔ ext inΓ) up
        helper (S^ inΔ up) (evar ext) (S^ inΓ) = S^ (helper inΔ ext inΓ) up
        helper (S= inΔ up) (evar-sol ext regA) (S^ inΓ) = S^ (helper inΔ ext inΓ) up
        helper (S= inΔ up) (svar ext regA) (S= inΓ) = S= (helper inΔ ext inΓ) up
⊆-⊢c-≫ ext (⊢c-var-= inΔ) (grd-var∙ x) = ⊥-elim (∋∙-∋=-false (⊆-∋∙' x ext) inΔ)
⊆-⊢c-≫ ext (⊢c-arr cloA cloA₁) (grd-arr grd grd₁) = grd-arr (⊆-⊢c-≫ ext cloA grd) (⊆-⊢c-≫ ext cloA₁ grd₁)
⊆-⊢c-≫ ext (⊢c-∀ cloA) (grd-∀ grd) = grd-∀ (⊆-⊢c-≫ (uvar ext) cloA grd)


⊆-⊢c-≫' : Γ ⊆ Δ
        → Γ ⊢c A
        → Γ ≫ A ⇘ A%
        → Δ ≫ A ⇘ A%
⊆-⊢c-≫' ext ⊢c-int grd-int = grd-int
⊆-⊢c-≫' ext (⊢c-var-∙ inΔ) (grd-var= x) = ⊥-elim (∋∙-∋:=-false inΔ x)
⊆-⊢c-≫' ext (⊢c-var-∙ inΔ) (grd-var∙ x) = grd-var∙ (⊆-∋∙ inΔ ext)
⊆-⊢c-≫' ext (⊢c-var-= inΔ) (grd-var= x) = grd-var= (⊆-∋:= x ext)
⊆-⊢c-≫' ext (⊢c-var-= inΔ) (grd-var∙ x) = ⊥-elim (∋∙-∋=-false x inΔ)
⊆-⊢c-≫' ext (⊢c-arr cloA cloA₁) (grd-arr grd grd₁) = grd-arr (⊆-⊢c-≫' ext cloA grd) (⊆-⊢c-≫' ext cloA₁ grd₁)
⊆-⊢c-≫' ext (⊢c-∀ cloA) (grd-∀ grd) = grd-∀ (⊆-⊢c-≫' (uvar ext) cloA grd)


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

≫-trans' : SRegular Γ
        → Γ ≫ A ⇘ B
        → Γ ◈ k ⇘ Γ'
        → k ¬εᵍ Γ
        → k ¬ε B
        → Γ' ≫ A ⇘ B
≫-trans' regΓ grd-int new ninΓ ninB = grd-int
≫-trans' regΓ (grd-var= x) new ninΓ ninB = grd-var= (◈-neq-∋:= x new (◈-∋:=-neq new x))
≫-trans' regΓ (grd-var∙ x) new ninΓ (¬ε-var x₁) = grd-var∙ (◈-neq-∋∙ x new x₁)
≫-trans' regΓ (grd-arr grd grd₁) new ninΓ (¬ε-arr ninB ninB₁) = grd-arr (≫-trans' regΓ grd new ninΓ ninB)
                                                                 (≫-trans' regΓ grd₁ new ninΓ ninB₁)
≫-trans' regΓ (grd-∀ grd) new ninΓ (¬ε-∀ ninB) = grd-∀ (≫-trans' (reg-S∙ regΓ) grd (◈S∙ new) (S∙ ninΓ) ninB)

≫-trans'0 : SRegular Γ
          → Γ ,∙ ≫ A ⇘ B
          → #0 ¬ε B
          → Γ ,^ ≫ A ⇘ B
≫-trans'0 regΓ grd1 ninA = ≫-trans' (reg-S∙ regΓ) grd1 ◈Z Z∙ ninA

≫-trans0 : SRegular Γ
          → Γ ⊢r B
          → Γ ,= B ≫ A₁ ⇘ A%
          → Γ ,∙ ≫ A ⇘ A₁
          → Γ ,= B ≫ A ⇘ A%
≫-trans0 {B = B} regT regB grd1 grd2 = ≫-trans {k = #0} (reg-S∙ regT) grd2 (∙⟹^0 (proj₂ (↑ty0-total B)) regB) Z∙ grd1


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

¬ε-≫-∙0 : #0 ¬ε A%
        → Γ ,∙ ≫ A ⇘ A%
        → #0 ¬ε A
¬ε-≫-∙0 ninA grd = ¬ε-≫-∙ ninA Z Z∙ grd

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
         → Γ ≫ A ⇘ A%
         → find A k j
find-≫-∙ (f-□ inA) ninΓ inΓ grd = f-□ (ε-≫-∙ inA inΓ ninΓ grd)
find-≫-∙ (f-iso iso) ninΓ inΓ (grd-var= x) = ⊥-elim (εᵍ-:=-false x ε-var ninΓ)
find-≫-∙ (f-iso iso) ninΓ inΓ (grd-var∙ x) = f-iso iso
find-≫-∙ (f-arr-l inA) ninΓ inΓ (grd-var= x) = ⊥-elim (εᵍ-:=-false x (ε-arr-l inA) ninΓ)
find-≫-∙ (f-arr-l inA) ninΓ inΓ (grd-arr grd grd₁) = f-arr-l (ε-≫-∙ inA inΓ ninΓ grd)
find-≫-∙ (f-arr-r ¬inA fd) ninΓ inΓ (grd-var= x) = ⊥-elim (εᵍ-:=-false x (ε-arr-r ¬inA (find-ε-gen fd)) ninΓ)
find-≫-∙ (f-arr-r ¬inA fd) ninΓ inΓ (grd-arr grd grd₁) = f-arr-r (¬ε-≫-∙ ¬inA inΓ ninΓ grd) (find-≫-∙ fd ninΓ inΓ grd₁)
find-≫-∙ (f-∀ fd) ninΓ inΓ (grd-var= x) = ⊥-elim (εᵍ-:=-false x (ε-∀ (find-ε-gen fd)) ninΓ)
find-≫-∙ (f-∀ fd) ninΓ inΓ (grd-∀ grd) = f-∀ (find-≫-∙ fd (S∙ ninΓ) (S∙ inΓ) grd)

find-≫-∙0 : find A% #0 j
          → Γ ,∙ ≫ A ⇘ A%
          → find A #0 j
find-≫-∙0 {Γ = Γ} fd grd = find-≫-∙ {Γ = Γ ,∙} fd Z∙ Z grd


≫-same : Γ ≫ A ⇘ A₁
       → Γ ◈ k ⇘ Γ'
       → Γ' ≫ A ⇘ A₂
       → k ¬ε A
       → A₁ ≡ A₂
≫-same grd-int new grd-int ¬ε-int = refl
≫-same (grd-var= x) new (grd-var= x₁) (¬ε-var x₂) = ◈-∋:=-neq-unique new x₂ x x₁
≫-same (grd-var= x) new (grd-var∙ x₁) (¬ε-var x₂) = let in2 = ◈-neq-∋:= x new x₂
                                                    in ⊥-elim (∋∙-∋:=-false x₁ in2)
≫-same (grd-var∙ x) new (grd-var= x₂) (¬ε-var x₁) = let in2 = ◈-neq-∋∙ x new x₁ in ⊥-elim (∋∙-∋:=-false in2 x₂)
≫-same (grd-var∙ x) new (grd-var∙ x₂) (¬ε-var x₁) = refl
≫-same (grd-arr grd1 grd3) new (grd-arr grd2 grd4) (¬ε-arr ninA ninA₁)
  with refl ← ≫-same grd1 new grd2 ninA
  with refl ← ≫-same grd3 new grd4 ninA₁ = refl
≫-same (grd-∀ grd1) new (grd-∀ grd2) (¬ε-∀ ninA) = cong `∀_ (≫-same grd1 (◈S∙ new) grd2 ninA)


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

≫-trans'' : SRegular Γ
        → Γ ≫ A ⇘ B
         → [ T / k ] Γ ∙⟹ Γ'
         → k ¬εᵍ Γ
         → Γ' ≫ A ⇘ C
         → Γ' ≫ B ⇘ C
≫-trans'' regΓ grd-int new ninΓ grd-int = grd-int
≫-trans'' regΓ (grd-var= x) new ninΓ (grd-var= x₁)
  with refl ← ∙⟹-:=-eq x new x₁ = ⊢r-≫-eq (∙⟹-⊢r (∋:=-⊢r regΓ x) new (εᵍ-:=-¬ε ninΓ x))
≫-trans'' regΓ (grd-var= x) new ninΓ (grd-var∙ x₁) = ⊥-elim (∙⟹-:=-∙-false x new x₁)
≫-trans'' regΓ (grd-var∙ x) new ninΓ (grd-var= x₁) = grd-var= x₁
≫-trans'' regΓ (grd-var∙ x) new ninΓ (grd-var∙ x₁) = grd-var∙ x₁
≫-trans'' regΓ (grd-arr grd1 grd3) new ninΓ (grd-arr grd2 grd4) = grd-arr (≫-trans'' regΓ grd1 new ninΓ grd2)
                                                                        (≫-trans'' regΓ grd3 new ninΓ grd4)
≫-trans'' {T = T} regΓ (grd-∀ grd1) new ninΓ (grd-∀ grd2) = grd-∀ (≫-trans'' (reg-S∙ regΓ) grd1 (∙⟹∙S new (proj₂ (↑ty0-total T))) (S∙ ninΓ) grd2)


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


¬ε-≫-∙' : k ¬ε A
       → Γ ∋∙ k
       → k ¬εᵍ Γ
       → Γ ≫ A ⇘ A%
       → k ¬ε A%
¬ε-≫-∙' ¬ε-int inΓ ninΓ grd-int = ¬ε-int
¬ε-≫-∙' (¬ε-var x) inΓ ninΓ (grd-var= x₁) = εᵍ-:=-¬ε ninΓ x₁
¬ε-≫-∙' (¬ε-var x) inΓ ninΓ (grd-var∙ x₁) = ¬ε-var x
¬ε-≫-∙' (¬ε-arr ninA ninA₁) inΓ ninΓ (grd-arr grd grd₁) = ¬ε-arr (¬ε-≫-∙' ninA inΓ ninΓ grd) (¬ε-≫-∙' ninA₁ inΓ ninΓ grd₁)
¬ε-≫-∙' (¬ε-∀ ninA) inΓ ninΓ (grd-∀ grd) = ¬ε-∀ (¬ε-≫-∙' ninA (S∙ inΓ) (S∙ ninΓ) grd)

ε-≫-∙' : k ε A
      → Γ ∋∙ k
      → k ¬εᵍ Γ
      → Γ ≫ A ⇘ A%
      → k ε A%
ε-≫-∙' ε-var inΓ ninΓ (grd-var= x) = ⊥-elim (∋∙-∋:=-false inΓ x)
ε-≫-∙' ε-var inΓ ninΓ (grd-var∙ x) = ε-var
ε-≫-∙' (ε-arr-l inA) inΓ ninΓ (grd-arr grd grd₁) = ε-arr-l (ε-≫-∙' inA inΓ ninΓ grd)
ε-≫-∙' (ε-arr-r ¬inA inA) inΓ ninΓ (grd-arr grd grd₁) = ε-arr-r (¬ε-≫-∙' ¬inA inΓ ninΓ grd) (ε-≫-∙' inA inΓ ninΓ grd₁)
ε-≫-∙' (ε-∀ inA) inΓ ninΓ (grd-∀ grd) = ε-∀ (ε-≫-∙' inA (S∙ inΓ) (S∙ ninΓ) grd)

find-≫-∙' : find A k j
         → k ¬εᵍ Γ
         → Γ ∋∙ k
         → Γ ≫ A ⇘ A%
         → find A% k j
find-≫-∙' (f-□ inA) ninΓ inΓ grd = f-□ (ε-≫-∙' inA inΓ ninΓ grd)
find-≫-∙' (f-iso iso) ninΓ inΓ (grd-var= x) = ⊥-elim (∋∙-∋:=-false inΓ x)
find-≫-∙' (f-iso iso) ninΓ inΓ (grd-var∙ x) = f-iso iso
find-≫-∙' (f-arr-l inA) ninΓ inΓ (grd-arr grd grd₁) = f-arr-l (ε-≫-∙' inA inΓ ninΓ grd)
find-≫-∙' (f-arr-r ¬inA fd) ninΓ inΓ (grd-arr grd grd₁) = f-arr-r (¬ε-≫-∙' ¬inA inΓ ninΓ grd) (find-≫-∙' fd ninΓ inΓ grd₁)
find-≫-∙' (f-∀ fd) ninΓ inΓ (grd-∀ grd) = f-∀ (find-≫-∙' fd (S∙ ninΓ) (S∙ inΓ) grd)

≫-same' : Γ ≫ A ⇘ A₁
       → Γ ◈ k ⇘ Γ'
       → Γ' ≫ A ⇘ A₂
       → k ¬ε A
       → A₁ ≡ A₂
≫-same' grd-int new grd-int ¬ε-int = refl
≫-same' (grd-var= x) new (grd-var= x₁) (¬ε-var x₂) = ◈-∋:=-neq-unique new x₂ x x₁
≫-same' (grd-var= x) new (grd-var∙ x₁) (¬ε-var x₂) = let in2 = ◈-neq-∋:= x new x₂
                                                    in ⊥-elim (∋∙-∋:=-false x₁ in2)
≫-same' (grd-var∙ x) new (grd-var= x₂) (¬ε-var x₁) = let in2 = ◈-neq-∋∙ x new x₁ in ⊥-elim (∋∙-∋:=-false in2 x₂)
≫-same' (grd-var∙ x) new (grd-var∙ x₂) (¬ε-var x₁) = refl
≫-same' (grd-arr grd1 grd3) new (grd-arr grd2 grd4) (¬ε-arr ninA ninA₁)
  with refl ← ≫-same' grd1 new grd2 ninA
  with refl ← ≫-same' grd3 new grd4 ninA₁ = refl
≫-same' (grd-∀ grd1) new (grd-∀ grd2) (¬ε-∀ ninA) = cong `∀_ (≫-same' grd1 (◈S∙ new) grd2 ninA)
