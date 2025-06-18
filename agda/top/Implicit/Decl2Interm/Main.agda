module Implicit.Decl2Interm.Main where

open import Implicit.Language.All
open import Implicit.Decl.All renaming (_⊢_#_≤_ to _⊢d_#_≤_)
open import Implicit.Interm.All renaming (_⊢_#_⌞_⌝_ to _⊢i_#_⌞_⌝_)

⊢r-≫-⊢c : Γ ≫ A ⇘ A%
        → Γ ⊢r A%
        → Γ ⊢c A
⊢r-≫-⊢c grd-int regA = ⊢c-int
⊢r-≫-⊢c grd-top regA = ⊢c-top
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
≫-trans regΓ grd-top new nin grd-top = grd-top
≫-trans regΓ (grd-var= x) new nin grd2 with ⊢r-≫-eq' (∙⟹-⊢r (∋:=-⊢r regΓ x) new (εᵍ-:=-¬ε nin x)) grd2
... | refl = grd-var= (∙⟹-∋:=-prv x new)
≫-trans regΓ (grd-var∙ x) new nin (grd-var= x₁) = grd-var= x₁
≫-trans regΓ (grd-var∙ x) new nin (grd-var∙ x₁) = grd-var∙ x₁
≫-trans regΓ (grd-arr grd1 grd3) new nin (grd-arr grd2 grd4)
  = grd-arr (≫-trans regΓ grd1 new nin grd2) (≫-trans regΓ grd3 new nin grd4)
≫-trans {T = T} regΓ (grd-∀ grd1) new nin (grd-∀ grd2)
  with ⟨ T' , upT ⟩ ← ↑ty0-total T
  = grd-∀ (≫-trans (reg-S∙ regΓ) grd1 (∙⟹∙S new upT) (S∙ nin) grd2)

◈-∋:=-neq : Γ ◈ k ⇘ Γ'
          → Γ ∋ X := A
          → X ≢ k
◈-∋:=-neq ◈Z (S∙ inΓ up) = λ ()
◈-∋:=-neq (◈S, new) (S, inΓ) = ◈-∋:=-neq new inΓ
◈-∋:=-neq (◈S∙ new) (S∙ inΓ up) = ≢-suc (◈-∋:=-neq new inΓ)
◈-∋:=-neq (◈S= new) (Z up) = λ ()
◈-∋:=-neq (◈S= new) (S= inΓ up) = ≢-suc (◈-∋:=-neq new inΓ)
◈-∋:=-neq (◈S^ new) (S^ inΓ up) = ≢-suc (◈-∋:=-neq new inΓ)

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
find-≫-∙ (f-∞ x) ninΓ inΓ grd = f-∞ (ε-≫-∙ x inΓ ninΓ grd)
find-≫-∙ (f-arr-𝕚-l x) ninΓ inΓ (grd-var= x₁) = ⊥-elim (εᵍ-:=-false x₁ (ε-arr-l x) ninΓ)
find-≫-∙ (f-arr-𝕚-l x) ninΓ inΓ (grd-arr grd grd₁) = f-arr-𝕚-l (ε-≫-∙ x inΓ ninΓ grd)
find-≫-∙ (f-arr-𝕚-r ¬inA fd) ninΓ inΓ (grd-var= x) = ⊥-elim (εᵍ-:=-false x (ε-arr-r ¬inA (find-ε-gen fd)) ninΓ)
find-≫-∙ (f-arr-𝕚-r ¬inA fd) ninΓ inΓ (grd-arr grd grd₁) = f-arr-𝕚-r (¬ε-≫-∙ ¬inA inΓ ninΓ grd) (find-≫-∙ fd ninΓ inΓ grd₁)
find-≫-∙ (f-arr-𝕔 ¬inA fd) ninΓ inΓ (grd-var= x) = ⊥-elim (εᵍ-:=-false x (ε-arr-r ¬inA (find-ε-gen fd)) ninΓ)
find-≫-∙ (f-arr-𝕔 ¬inA fd) ninΓ inΓ (grd-arr grd grd₁) = f-arr-𝕔 (¬ε-≫-∙ ¬inA inΓ ninΓ grd) (find-≫-∙ fd ninΓ inΓ grd₁)
find-≫-∙ (f-∀-𝕚 fd upj) ninΓ inΓ (grd-var= x) = ⊥-elim (εᵍ-:=-false x (ε-∀ (find-ε-gen fd)) ninΓ)
find-≫-∙ (f-∀-𝕚 fd upj) ninΓ inΓ (grd-∀ grd) = f-∀-𝕚 (find-≫-∙ fd (S∙ ninΓ) (S∙ inΓ) grd) upj
find-≫-∙ (f-∀-𝕔 fd upj) ninΓ inΓ (grd-var= x) = ⊥-elim (εᵍ-:=-false x (ε-∀ (find-ε-gen fd)) ninΓ)
find-≫-∙ (f-∀-𝕔 fd upj) ninΓ inΓ (grd-∀ grd) = f-∀-𝕔 (find-≫-∙ fd (S∙ ninΓ) (S∙ inΓ) grd) upj
find-≫-∙ (f-𝕥 fd upj) ninΓ inΓ (grd-var= x) = ⊥-elim (εᵍ-:=-false x (ε-∀ (find-ε-gen fd)) ninΓ)
find-≫-∙ (f-𝕥 fd upj) ninΓ inΓ (grd-∀ grd) = f-𝕥 (find-≫-∙ fd (S∙ ninΓ) (S∙ inΓ) grd) upj
find-≫-∙ (f-iso iso) ninΓ inΓ (grd-var= x) = ⊥-elim (εᵍ-:=-false x ε-var ninΓ)
find-≫-∙ (f-iso iso) ninΓ inΓ (grd-var∙ x) = f-iso iso

find-≫-∙0 : find A% #0 j
          → Γ ,∙ ≫ A ⇘ A%
          → find A #0 j
find-≫-∙0 {Γ = Γ} fd grd = find-≫-∙ {Γ = Γ ,∙} fd Z∙ Z grd

complete+ : Γ ⊢d j # A% ≤ B
          → Γ ≫ A ⇘ A%
          → Γ ⊢i j # A ⌞ ≤⁺ ⌝ B


complete- : Γ ⊢d ∞ # A ≤ B%
          → Γ ≫ B ⇘ B%
          → Γ ⊢i ∞ # A ⌞ ≤⁻ ⌝ B

complete+ (s-refl regΔ cloA) grd = s-refl regΔ (⊢r-≫-⊢c grd cloA) grd
complete+ (s-int regΔ) grd-int = s-int regΔ
complete+ (s-int regΔ) (grd-var= x) = s-svar-l x (s-int regΔ)
-- s-svar-l regΔ x
complete+ (s-var-∙ regΔ inΔ) (grd-var= x) = s-svar-l x (s-var-∙ regΔ inΔ)
-- s-svar-l regΔ x
complete+ (s-var-∙ regΔ inΔ) (grd-var∙ x) = s-var-∙ regΔ x
-- s-var-∙ regΔ x
complete+ (s-arr₁ s s₁) (grd-var= x)
  with ⊢r-arr regA regA₁ ← ∋:=-⊢r (s2-sregular s) x
  = s-svar-l x (s-arr₁ (complete- s (⊢r-≫-eq regA)) (complete+ s₁ (⊢r-≫-eq regA₁)))
complete+ (s-arr₁ s s₁) (grd-arr grd grd₁) = s-arr₁ (complete- s grd) (complete+ s₁ grd₁)
complete+ (s-arr₂ s s₁) (grd-var= x) = s-svar-𝕚 x (s-arr₂ (complete- s (⊢r-≫-eq (s2-⊢r-r s))) (complete+ s₁ (⊢r-≫-eq (s2-⊢r-l s₁))))
complete+ (s-arr₂ s s₁) (grd-arr grd grd₁) = s-arr₂ (complete- s grd) (complete+ s₁ grd₁)
complete+ (s-arr₃ regA s) (grd-var= x) = s-svar-𝕔 x (s-arr₃ (⊢r-⊢c regA) (⊢r-≫-eq regA) (complete+ s (⊢r-≫-eq (s2-⊢r-l s))))
complete+ (s-arr₃ regA s) (grd-arr grd grd₁) = s-arr₃ (⊢r-≫-⊢c grd regA) grd (complete+ s grd₁)
complete+ s'@(s-∀ s) (grd-var= x)
  with ⊢r-∀ regA ← ∋:=-⊢r (s2-sregular s') x
  = s-svar-l x (s-∀ (complete+ s (⊢r-≫-eq regA)))
complete+ (s-∀ s) (grd-∀ grd) = s-∀ (complete+ s grd)
complete+ (s-∀l grd₁ regA s case-𝕚 fd upC upD upj) (grd-var= x)
  = s-svar-𝕚 x (s-∀l (complete+ s grd₁) case-𝕚 fd upC upD upj)
complete+ (s-∀l grd₁ regA s case-𝕔 fd upC upD upj) (grd-var= x)
  = s-svar-𝕔 x (s-∀l (complete+ s grd₁) case-𝕔 fd upC upD upj)
complete+ (s-∀l-no-appear grd₁ regA s case-𝕚 fd upC upD upj) (grd-var= x)
  = s-svar-𝕚 x (s-∀l-no-appear (complete+ s grd₁) case-𝕚 fd upC upD upj)
complete+ (s-∀l-no-appear grd₁ regA s case-𝕔 fd upC upD upj) (grd-var= x)
  = s-svar-𝕔 x (s-∀l-no-appear (complete+ s grd₁) case-𝕔 fd upC upD upj)
complete+ (s-∀l grd₁ regA s case-𝕚 fd upC upD upj) (grd-∀ grd)
  with reg-S= regΓ regA ← s2-sregular s
  = s-∀l (complete+ s (≫-trans0 regΓ regA grd₁ grd)) case-𝕚 (find-≫-∙0 fd grd) upC upD upj
complete+ (s-∀l grd₁ regA s case-𝕔 fd upC upD upj) (grd-∀ grd)
  with reg-S= regΓ regA ← s2-sregular s
  = s-∀l (complete+ s (≫-trans0 regΓ regA grd₁ grd)) case-𝕔 (find-≫-∙0 fd grd) upC upD upj
complete+ (s-∀l-no-appear grd₁ regA s case-𝕚 fd upC upD upj) (grd-∀ grd)
  with reg-S^ regΓ ← s2-sregular s
  with ⟨ A' , upA ⟩ ← ↑ty-surjective fd
  with refl ← ⊢r-≫-eq' (⊢r-weaken^0 (⊢r-strengthen∙0 regA upA) upA) grd₁
  = s-∀l-no-appear (complete+ s (≫-trans'0 regΓ grd fd)) case-𝕚 (¬ε-≫-∙0 fd grd) upC upD upj
complete+ (s-∀l-no-appear grd₁ regA s case-𝕔 fd upC upD upj) (grd-∀ grd)
  with reg-S^ regΓ ← s2-sregular s
  with ⟨ A' , upA ⟩ ← ↑ty-surjective fd
  with refl ← ⊢r-≫-eq' (⊢r-weaken^0 (⊢r-strengthen∙0 regA upA) upA) grd₁
  = s-∀l-no-appear (complete+ s (≫-trans'0 regΓ grd fd)) case-𝕔 (¬ε-≫-∙0 fd grd) upC upD upj
complete+ (s-tapp x regA s upj) (grd-var= x₁) = s-svar-𝕥 x₁ (s-tapp (complete+ s x) upj)
complete+ (s-tapp x regA s upj) (grd-∀ grd)
  with reg-S= regΓ regA ← s2-sregular s = s-tapp (complete+ s (≫-trans0 regΓ regA x grd)) upj
complete+ (s-top regΔ) x = s-top regΔ

complete- (s-int regΔ) grd-int = s-int regΔ
complete- (s-int regΔ) (grd-var= x) = s-svar-r x (s-int regΔ)
-- s-svar-r regΔ x
complete- (s-var-∙ regΔ inΔ) (grd-var= x) = s-svar-r x (s-var-∙ regΔ inΔ)
-- s-svar-r regΔ x
complete- (s-var-∙ regΔ inΔ) (grd-var∙ x) = s-var-∙ regΔ x
complete- (s-arr₁ s s₁) (grd-var= x)
  with ⊢r-arr regA regA₁ ← ∋:=-⊢r (s2-sregular s) x
  = s-svar-r x (s-arr₁ (complete+ s (⊢r-≫-eq regA)) (complete- s₁ (⊢r-≫-eq regA₁)))
complete- (s-arr₁ s s₁) (grd-arr grd grd₁) = s-arr₁ (complete+ s grd) (complete- s₁ grd₁)
complete- s'@(s-∀ s) (grd-var= x)
  with ⊢r-∀ regA ← ∋:=-⊢r (s2-sregular s') x
  = s-svar-r x (s-∀ (complete- s (⊢r-≫-eq regA)))
complete- (s-∀ s) (grd-∀ grd) = s-∀ (complete- s grd)
complete- (s-top regΔ) grd-top = s-top regΔ
complete- (s-top regΔ) (grd-var= x) = s-svar-r x (s-top regΔ)

complete0 : Γ ⊢d j # A ≤ B
          → Γ ⊢i j # A ⌞ ≤⁺ ⌝ B
complete0 s = complete+ s (⊢r-≫-eq (s2-⊢r-l s))
