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
s-trans' (s-∀l regB st s1 fd) (s-arr₂ s2 s3) = s-∀l regB st (s-trans' s1 (s-arr₂ s2 s3)) fd
s-trans' (s-∀l regB st s1 fd) (s-arr₃ regA s2) = s-∀l regB st (s-trans' s1 (s-arr₃ regA s2)) fd
s-trans' (s-∀l-no-appear regB st s1 fd) (s-arr₂ s2 s3) = s-∀l-no-appear regB st (s-trans' s1 (s-arr₂ s2 s3)) fd
s-trans' (s-∀l-no-appear regB st s1 fd) (s-arr₃ regA s2) = s-∀l-no-appear regB st (s-trans' s1 (s-arr₃ regA s2)) fd


infix 3 _≋_
data _≋_ : Mask → Mask → Set where
  Z≋ : ∀ {nj}
       → `■ ≋ nj
  S≋ : ∀ {nj}
       → j ≋ nj
     → (i · j) ≋ (i · nj)
  refl≋ : j ≋ j

≋-isoinf : ∀ {nj}
         → j ≋ nj
         → □like j
         → □like nj
≋-isoinf (S≋ refl≋) □like-Z = □like-Z
≋-isoinf (S≋ nj) (□like-S wlike) = □like-S (≋-isoinf nj wlike)
≋-isoinf refl≋ wlike = wlike

find-≋ : ∀ {nj}
       → find A k j
       → j ≋ nj
       → find A k nj
find-≋ (f-arr-l x) (S≋ ~j) = f-arr-l x
find-≋ (f-arr-r ¬inA fd) (S≋ ~j) = f-arr-r ¬inA (find-≋ fd ~j)
find-≋ (f-∀ fd) (S≋ {nj = nj} ~j)
  = f-∀ (find-≋ fd (S≋ ~j))
find-≋ (f-iso iso) (S≋ ~j) = f-iso (≋-isoinf (S≋ ~j) iso)
find-≋ (f-iso iso) refl≋ = f-iso iso
find-≋ fd refl≋ = fd

s-trans-∞ : Γ ⊢d `□ # A ≤ B
          → Γ ⊢d `□ # B ≤ C
          → Γ ⊢d `□ # A ≤ C
s-trans-∞ (s-int regΔ) (s-int regΔ₁) = s-int regΔ
s-trans-∞ (s-var-∙ regΔ inΔ) s2 = s2
s-trans-∞ (s-arr₁ s1 s3) (s-arr₁ s2 s4) = s-arr₁ (s-trans-∞ s2 s1) (s-trans-∞ s3 s4)
s-trans-∞ (s-∀ s1) (s-∀ s2) = s-∀ (s-trans-∞ s1 s2)

s-trans-∞-eq : Γ ⊢d `□ # A ≤ B
             → A ≡ B
s-trans-∞-eq (s-int regΔ) = refl
s-trans-∞-eq (s-var-∙ regΔ inΔ) = refl
s-trans-∞-eq (s-arr₁ s s₁) = cong₂ _`→_ (sym (s-trans-∞-eq s)) (s-trans-∞-eq s₁)
s-trans-∞-eq (s-∀ s) = cong `∀_ (s-trans-∞-eq s)


s-refl-∞ : SRegular Γ
         → Γ ⊢r A
         → Γ ⊢d `□ # A ≤ A
s-refl-∞ regΓ ⊢r-int = s-int regΓ
s-refl-∞ regΓ (⊢r-var-∙ inΓ) = s-var-∙ regΓ inΓ
s-refl-∞ regΓ (⊢r-arr regA regA₁) = s-arr₁ (s-refl-∞ regΓ regA) (s-refl-∞ regΓ regA₁)
s-refl-∞ regΓ (⊢r-∀ regA) = s-∀ (s-refl-∞ (reg-S∙ regΓ) regA)

s-trans : Γ ⊢d j # A ≤ B
        → j ≋ j'
        → Γ ⊢d j' # B ≤ C
        → Γ ⊢d j' # A ≤ C
s-trans (s-refl regΔ cloA) ~j s2 = s2
s-trans (s-arr₂ s1 s3) (S≋ ~j) (s-arr₂ s2 s4) = s-arr₂ (s-trans-∞ s2 s1) (s-trans s3 ~j s4)
s-trans (s-arr₃ regA s1) (S≋ ~j) (s-arr₃ regA₁ s2) = s-arr₃ regA (s-trans s1 ~j s2)
s-trans (s-∀l regB st s1 fd) (S≋ {nj = nj} ~j) (s-arr₂ s2 s3)
  = s-∀l regB st (s-trans s1 (S≋ ~j) (s-arr₂ s2 s3)) (find-≋ fd (S≋ ~j))
s-trans (s-∀l-no-appear regB st s1 fd) (S≋ ~j) (s-arr₃ regA s3)
  = s-∀l-no-appear regB st (s-trans s1 (S≋ ~j) (s-arr₃ regA s3)) fd
s-trans s1 refl≋ s2 = s-trans' s1 s2
s-trans (s-∀l regB st x fd) (S≋ x₁) (s-arr₃ regA x₂)
  = s-∀l regB st (s-trans x (S≋ x₁) (s-arr₃ regA x₂)) (find-≋ fd (S≋ x₁))
s-trans (s-∀l-no-appear regB st x fd) (S≋ x₁) (s-arr₂ x₂ x₃)
  = s-∀l-no-appear regB st (s-trans x (S≋ x₁) (s-arr₂ x₂ x₃)) fd
