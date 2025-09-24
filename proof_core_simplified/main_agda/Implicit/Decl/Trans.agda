module Implicit.Decl.Trans where

open import Implicit.Language.All
open import Implicit.Decl.Subtyping


s-trans' : Γ ⊢d j # A ≤ B
        → Γ ⊢d j # B ≤ C
        → Γ ⊢d j # A ≤ C
s-trans' (s-refl regΔ cloA) (s-refl regΔ₁ cloA₁) = s-refl regΔ cloA₁
s-trans' (s-int regΔ) (s-int regΔ₁) = s-int regΔ
s-trans' (s-var-∙ regΔ inΔ) (s-var-∙ regΔ₁ inΔ₁) = s-var-∙ regΔ inΔ₁
s-trans' (s-arr₁ s1 s3) (s-arr₁ s2 s4) = s-arr₁ (s-trans' s2 s1) (s-trans' s3 s4)
s-trans' (s-arr₂ s1 s3) (s-arr₂ s2 s4) = s-arr₂ (s-trans' s2 s1) (s-trans' s3 s4)
s-trans' (s-arr₃ regA s1) (s-arr₃ regA₁ s2) = s-arr₃ regA (s-trans' s1 s2)
s-trans' (s-∀ s1) (s-∀ s2) = s-∀ (s-trans' s1 s2)
s-trans' (s-∀l regB st s1 ic fd) (s-arr₂ s2 s3) = s-∀l regB st (s-trans' s1 (s-arr₂ s2 s3)) ic fd
s-trans' (s-∀l regB st s1 ic fd) (s-arr₃ regA s2) = s-∀l regB st (s-trans' s1 (s-arr₃ regA s2)) ic fd
s-trans' (s-∀l-no-appear regB st s1 ic fd) (s-arr₂ s2 s3) = s-∀l-no-appear regB st (s-trans' s1 (s-arr₂ s2 s3)) ic fd
s-trans' (s-∀l-no-appear regB st s1 ic fd) (s-arr₃ regA s2) = s-∀l-no-appear regB st (s-trans' s1 (s-arr₃ regA s2)) ic fd


infix 3 _≋_
data _≋_ : Counter → Counter → Set where
  Z≋ : ∀ {nj}
       → Z ≋ nj
  𝕚≋ : ∀ {nj}
       → j ≋ nj
     → 𝕚 j ≋ 𝕚 nj
  𝕔≋ : ∀ {nj}
     → j ≋ nj
     → 𝕔 j ≋ 𝕔 nj
  refl≋ : j ≋ j

≋-isoinf : ∀ {nj}
         → j ≋ nj
         → IsoInf j
         → IsoInf nj
≋-isoinf (𝕚≋ refl≋) i∞-z = i∞-z
≋-isoinf (𝕚≋ newj) (i∞-i iso) = i∞-i (≋-isoinf newj iso)
≋-isoinf refl≋ iso = iso

find-≋ : ∀ {nj}
       → find A k j
       → j ≋ nj
       → find A k nj
find-≋ (f-arr-𝕚-l x) (𝕚≋ ~j) = f-arr-𝕚-l x
find-≋ (f-arr-𝕚-r ¬inA fd) (𝕚≋ ~j) = f-arr-𝕚-r ¬inA (find-≋ fd ~j)
find-≋ (f-arr-𝕔 ¬inA fd) (𝕔≋ ~j) = f-arr-𝕔 ¬inA (find-≋ fd ~j)
find-≋ (f-∀-𝕚 fd) (𝕚≋ {nj = nj} ~j)
  = f-∀-𝕚 (find-≋ fd (𝕚≋ ~j))
find-≋ (f-∀-𝕔 fd) (𝕔≋ {nj = nj} ~j)
  = f-∀-𝕔 (find-≋ fd (𝕔≋ ~j))
find-≋ (f-iso iso) (𝕚≋ ~j) = f-iso (≋-isoinf (𝕚≋ ~j) iso)
find-≋ (f-iso iso) refl≋ = f-iso iso
find-≋ fd refl≋ = fd

s-trans-∞ : Γ ⊢d ∞ # A ≤ B
          → Γ ⊢d ∞ # B ≤ C
          → Γ ⊢d ∞ # A ≤ C
s-trans-∞ (s-int regΔ) (s-int regΔ₁) = s-int regΔ
s-trans-∞ (s-var-∙ regΔ inΔ) s2 = s2
s-trans-∞ (s-arr₁ s1 s3) (s-arr₁ s2 s4) = s-arr₁ (s-trans-∞ s2 s1) (s-trans-∞ s3 s4)
s-trans-∞ (s-∀ s1) (s-∀ s2) = s-∀ (s-trans-∞ s1 s2)

s-trans-∞-eq : Γ ⊢d ∞ # A ≤ B
             → A ≡ B
s-trans-∞-eq (s-int regΔ) = refl
s-trans-∞-eq (s-var-∙ regΔ inΔ) = refl
s-trans-∞-eq (s-arr₁ s s₁) = cong₂ _`→_ (sym (s-trans-∞-eq s)) (s-trans-∞-eq s₁)
s-trans-∞-eq (s-∀ s) = cong `∀_ (s-trans-∞-eq s)


s-refl-∞ : SRegular Γ
         → Γ ⊢r A
         → Γ ⊢d ∞ # A ≤ A
s-refl-∞ regΓ ⊢r-int = s-int regΓ
s-refl-∞ regΓ (⊢r-var-∙ inΓ) = s-var-∙ regΓ inΓ
s-refl-∞ regΓ (⊢r-arr regA regA₁) = s-arr₁ (s-refl-∞ regΓ regA) (s-refl-∞ regΓ regA₁)
s-refl-∞ regΓ (⊢r-∀ regA) = s-∀ (s-refl-∞ (reg-S∙ regΓ) regA)

s-trans : Γ ⊢d j # A ≤ B
        → j ≋ j'
        → Γ ⊢d j' # B ≤ C
        → Γ ⊢d j' # A ≤ C
s-trans (s-refl regΔ cloA) ~j s2 = s2
s-trans (s-arr₂ s1 s3) (𝕚≋ ~j) (s-arr₂ s2 s4) = s-arr₂ (s-trans-∞ s2 s1) (s-trans s3 ~j s4)
s-trans (s-arr₃ regA s1) (𝕔≋ ~j) (s-arr₃ regA₁ s2) = s-arr₃ regA (s-trans s1 ~j s2)
s-trans (s-∀l regB st s1 () fd) Z≋ (s-refl regΔ cloA)
s-trans (s-∀l regB st s1 () fd) Z≋ (s-arr₁ s2 s3)
s-trans (s-∀l regB st s1 ic fd) (𝕚≋ {nj = nj} ~j) (s-arr₂ s2 s3)
  = s-∀l regB st (s-trans s1 (𝕚≋ ~j) (s-arr₂ s2 s3)) case-𝕚 (find-≋ fd (𝕚≋ ~j))
s-trans (s-∀l regB st s1 ic fd) (𝕔≋ {nj = nj} ~j) (s-arr₃ regA s2)
  = s-∀l regB st (s-trans s1 (𝕔≋ ~j) (s-arr₃ regA s2)) case-𝕔 (find-≋ fd (𝕔≋ ~j))
s-trans (s-∀l-no-appear regB st s1 ic fd) (𝕚≋ ~j) (s-arr₂ s2 s3)
  = s-∀l-no-appear regB st (s-trans s1 (𝕚≋ ~j) (s-arr₂ s2 s3)) case-𝕚 fd
s-trans (s-∀l-no-appear regB st s1 ic fd) (𝕔≋ ~j) (s-arr₃ regA s3)
  = s-∀l-no-appear regB st (s-trans s1 (𝕔≋ ~j) (s-arr₃ regA s3)) case-𝕔 fd
s-trans s1 refl≋ s2 = s-trans' s1 s2
