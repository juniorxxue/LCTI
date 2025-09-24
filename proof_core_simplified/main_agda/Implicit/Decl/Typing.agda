{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --allow-incomplete-matches #-}
module Implicit.Decl.Typing where

open import Implicit.Language.All
open import Implicit.Decl.Subtyping

----------------------------------------------------------------------
--+                             Typing                             +--
----------------------------------------------------------------------

infix 3 _⊢d_#_⦂_
data _⊢d_#_⦂_ : Env n m → Counter → Term n m → Type m → Set where
  ⊢lit : ∀ {num : ℕ}
    → (regΓ : TRegular Γ)
    → Γ ⊢d Z # (lit num) ⦂ Int
  ⊢var :
      (regΓ : TRegular Γ)
    → (x∈Γ : Γ ∋ x ⦂ A)
    → Γ ⊢d Z # ` x ⦂ A
  ⊢ann :
      Γ ⊢d ∞ # e ⦂ A
    → Γ ⊢d Z # (e ⦂ A) ⦂ A
  ⊢lam₁ :
      Γ , A ⊢d ∞ # e ⦂ B
    → Γ ⊢d ∞ # ƛ e ⦂ A `→ B
  ⊢lam₂ :
      Γ , A ⊢d j # e ⦂ B
    → Γ ⊢d 𝕚 j # ƛ e ⦂ A `→ B
  ⊢app₁ :
      Γ ⊢d 𝕔 j # e₁ ⦂ A `→ B
    → Γ ⊢d ∞ # e₂ ⦂ A
    → Γ ⊢d j # e₁ · e₂ ⦂ B
  ⊢app₂ :
      Γ ⊢d 𝕚 j # e₁ ⦂ A `→ B
    → Γ ⊢d Z # e₂ ⦂ A
    → Γ ⊢d j # e₁ · e₂ ⦂ B
  ⊢sub :
      Γ ⊢d Z # g ⦂ A
    → (B≤A : Γ ⋈ ⊢d j # A ≤ B)
    → (gc : GenericConsumer g)
    → (j≢Z : NonZ j)
    → Γ ⊢d j # g ⦂ B
  ⊢tabs :
      Γ ,∙ ⊢d Z # e ⦂ A
    → Γ ⊢d Z # Λ e ⦂ `∀ A
  ⊢tabs-∞ :
      Γ ,∙ ⊢d ∞ # e ⦂ A
    → Γ ⊢d ∞ # Λ e ⦂ `∀ A
  ⊢tapp :
      Γ ⊢d Z # e ⦂ `∀ B
    → (regA : Γ ⊢r A)
    → (st : ⟦ A ⟧ B ⇘ B*)
    → (s : Γ ⋈ ⊢d j # B* ≤ C)
    → Γ ⊢d j # e ⓪ A ⦂ C

s-sregular : Γ ⊢d j # A ≤ B
           → SRegular Γ
s-sregular (s-refl regΔ cloA) = regΔ
s-sregular (s-int regΔ) = regΔ
s-sregular (s-var-∙ regΔ inΔ) = regΔ
s-sregular (s-arr₁ s s₁) = s-sregular s
s-sregular (s-arr₂ s s₁) = s-sregular s
s-sregular (s-arr₃ regA s) = s-sregular s
s-sregular (s-∀ s) with s-sregular s
... | reg-S∙ r = r
s-sregular (s-∀l regB st s ic fd) = s-sregular s
s-sregular (s-∀l-no-appear regB st x ic fd) = s-sregular x

t-tregular : Γ ⊢d j # e ⦂ A
           → TRegular Γ
t-tregular (⊢lit regΓ) = regΓ
t-tregular (⊢var regΓ x∈Γ) = regΓ
t-tregular (⊢ann ⊢e) = t-tregular ⊢e
t-tregular (⊢lam₁ ⊢e) with t-tregular ⊢e
... | reg-S, r regA = r
t-tregular (⊢lam₂ ⊢e) with t-tregular ⊢e
... | reg-S, r regA = r
t-tregular (⊢app₁ ⊢e ⊢e₁) = t-tregular ⊢e
t-tregular (⊢app₂ ⊢e ⊢e₁) = t-tregular ⊢e
t-tregular (⊢sub ⊢e B≤A gc j≢Z) = t-tregular ⊢e
t-tregular (⊢tabs ⊢e) with t-tregular ⊢e
... | reg-S∙ r = r
t-tregular (⊢tabs-∞ ⊢e) with t-tregular ⊢e
... | reg-S∙ r = r
t-tregular (⊢tapp ⊢e regA st s) = t-tregular ⊢e

t-⊢r : Γ ⊢d j # e ⦂ A
     → Γ ⊢r A
t-⊢r (⊢lit regΓ) = ⊢r-int
t-⊢r (⊢var regΓ x∈Γ) = ∋⦂-⊢r regΓ x∈Γ
t-⊢r (⊢ann ⊢e) = t-⊢r ⊢e
t-⊢r (⊢lam₁ ⊢e) with t-tregular ⊢e
... | reg-S, r regA = ⊢r-arr regA (⊢r-strengthen,0 (t-⊢r ⊢e))
t-⊢r (⊢lam₂ ⊢e) with t-tregular ⊢e
... | reg-S, r regA = ⊢r-arr regA (⊢r-strengthen,0 (t-⊢r ⊢e))
t-⊢r (⊢app₁ ⊢e ⊢e₁) with t-⊢r ⊢e
... | ⊢r-arr r r₁ = r₁
t-⊢r (⊢app₂ ⊢e ⊢e₁) with t-⊢r ⊢e
... | ⊢r-arr r r₁ = r₁
t-⊢r (⊢sub ⊢e B≤A gc j≢Z) = ⊢r-𝕣' (s1-⊢r-r B≤A)
t-⊢r (⊢tabs ⊢e) = ⊢r-∀ (t-⊢r ⊢e)
t-⊢r (⊢tabs-∞ ⊢e) = ⊢r-∀ (t-⊢r ⊢e)
t-⊢r (⊢tapp ⊢e regA st s) = {!!}


infix 3 _≋_
data _≋_ : Counter → Counter → Set where
  Z≋ : ∀ {nj : Counter}
       → Z ≋ nj
  𝕚≋ : ∀ {nj}
       → j ≋ nj
     → 𝕚 j ≋ 𝕚 nj
  𝕔≋ : ∀ {nj}
     → j ≋ nj
     → 𝕔 j ≋ 𝕔 nj
--  ≋refl : j ≋ j


iso-≋-false : ∀ {nj}
            → j ≋ nj
            → IsoInf j
            → ⊥
iso-≋-false (𝕚≋ ~j) (i∞-i iso) = iso-≋-false ~j iso

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
find-≋ (f-iso iso) ~j = ⊥-elim (iso-≋-false ~j iso)


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


postulate
  gen-sub : Γ ⊢d j # e ⦂ A
        → j ≋ j'
        → Γ ⋈ ⊢d j' # A ≤ B
        → Γ ⊢d j' # e ⦂ B

gen-sub0 : Γ ⊢d Z # g ⦂ A
         → Γ ⋈ ⊢d j # A ≤ B
         → Γ ⊢d j # g ⦂ B
gen-sub0 ⊢e s = gen-sub ⊢e Z≋ s
