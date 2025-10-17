module Implicit.Decl.Typing where

open import Implicit.Language.All
open import Implicit.Decl.Subtyping

----------------------------------------------------------------------
--+                             Typing                             +--
----------------------------------------------------------------------

infix 3 _⊢d_#_⦂_
data _⊢d_#_⦂_ : Env n m → Mask → Term n m → Type m → Set where
  ⊢lit : ∀ {num : ℕ}
    → (regΓ : TRegular Γ)
    → Γ ⊢d `■ # (lit num) ⦂ Int
  ⊢var :
      (regΓ : TRegular Γ)
    → (x∈Γ : Γ ∋ x ⦂ A)
    → Γ ⊢d `■ # ` x ⦂ A
  ⊢ann :
      Γ ⊢d `□ # e ⦂ A
    → Γ ⊢d `■ # (e ⦂ A) ⦂ A
  ⊢lam₁ :
      Γ , A ⊢d `□ # e ⦂ B
    → Γ ⊢d `□ # ƛ e ⦂ A `→ B
  ⊢lam₂ :
      Γ , A ⊢d j # e ⦂ B
    → Γ ⊢d □ · j # ƛ e ⦂ A `→ B
  ⊢app :
      Γ ⊢d (fp i) · j # e₁ ⦂ A `→ B
    → Γ ⊢d ` i # e₂ ⦂ A
    → Γ ⊢d j # e₁ · e₂ ⦂ B
  ⊢sub :
      Γ ⊢d `■ # g ⦂ A
    → (B≤A : Γ ⋈ ⊢d j # A ≤ B)
    → (gc : GenericConsumer g)
    → (j≢Z : NonZ j)
    → Γ ⊢d j # g ⦂ B
  ⊢tabs :
      Γ ,∙ ⊢d ` i # e ⦂ A
    → Γ ⊢d ` i # Λ e ⦂ `∀ A
  ⊢tapp :
      Γ ⊢d `■ # e ⦂ `∀ B
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
s-sregular (s-∀l regB st s fd) = s-sregular s
s-sregular (s-∀l-no-appear regB st x fd) = s-sregular x

t-tregular : Γ ⊢d j # e ⦂ A
           → TRegular Γ
t-tregular (⊢lit regΓ) = regΓ
t-tregular (⊢var regΓ x∈Γ) = regΓ
t-tregular (⊢ann ⊢e) = t-tregular ⊢e
t-tregular (⊢lam₁ ⊢e) with t-tregular ⊢e
... | reg-S, r regA = r
t-tregular (⊢lam₂ ⊢e) with t-tregular ⊢e
... | reg-S, r regA = r
t-tregular (⊢app ⊢e ⊢e₁) = t-tregular ⊢e
t-tregular (⊢sub ⊢e B≤A gc j≢Z) = t-tregular ⊢e
t-tregular (⊢tabs ⊢e) with t-tregular ⊢e
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
t-⊢r (⊢app ⊢e ⊢e₁) with t-⊢r ⊢e
... | ⊢r-arr r r₁ = r₁
t-⊢r (⊢sub ⊢e B≤A gc j≢Z) = ⊢r-𝕣' (s1-⊢r-r B≤A)
t-⊢r (⊢tabs ⊢e) = ⊢r-∀ (t-⊢r ⊢e)
t-⊢r (⊢tapp ⊢e regA st s) = ⊢r-𝕣' (s1-⊢r-r s)


infix 3 _≋_
data _≋_ : Mask → Mask → Set where
  Z≋ : ∀ {nj : Mask}
       → ` ■ ≋ nj
  S≋ : ∀ {nj}
       → j ≋ nj
     → i · j ≋ i · nj

iso-≋-false : ∀ {nj}
            → j ≋ nj
            → □like j
            → ⊥
iso-≋-false (S≋ newj) (□like-S wlike) = iso-≋-false newj wlike

find-≋ : ∀ {nj}
       → find A k j
       → j ≋ nj
       → find A k nj
find-≋ (f-arr-l x) (S≋ ~j) = f-arr-l x
find-≋ (f-arr-r ¬inA fd) (S≋ ~j) = f-arr-r ¬inA (find-≋ fd ~j)
find-≋ (f-∀ fd) (S≋ {nj = nj} ~j)
  = f-∀ (find-≋ fd (S≋ ~j))
find-≋ (f-iso iso) ~j = ⊥-elim (iso-≋-false ~j iso)


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
s-trans (s-∀l regB st s1 fd) (S≋ {nj = nj} ~j) (s-arr₃ regA s2)
  = s-∀l regB st (s-trans s1 (S≋ ~j) (s-arr₃ regA s2)) (find-≋ fd (S≋ ~j))
s-trans (s-∀l-no-appear regB st s1 fd) (S≋ ~j) (s-arr₂ s2 s3)
  = s-∀l-no-appear regB st (s-trans s1 (S≋ ~j) (s-arr₂ s2 s3)) fd
s-trans (s-∀l-no-appear regB st s1 fd) (S≋ ~j) (s-arr₃ regA s3)
  = s-∀l-no-appear regB st (s-trans s1 (S≋ ~j) (s-arr₃ regA s3)) fd



gen-sub : Γ ⊢d j # e ⦂ A
        → j ≋ j'
        → Γ ⋈ ⊢d j' # A ≤ B
        → Γ ⊢d j' # e ⦂ B
gen-sub {j' = ` ■} ⊢e Z≋ (s-refl regΔ cloA) = ⊢e

gen-sub {j' = ` □} (⊢lit regΓ) Z≋ s = ⊢sub (⊢lit regΓ) s gc-i nz-□
gen-sub {j' = ` □} (⊢var regΓ x∈Γ) Z≋ s = ⊢sub (⊢var regΓ x∈Γ) s gc-var nz-□
gen-sub {j' = ` □} (⊢ann ⊢e) Z≋ s = ⊢sub (⊢ann ⊢e) s gc-ann nz-□
gen-sub {j' = ` □} (⊢app {i = □} ⊢e ⊢e₁) Z≋ s = ⊢app ((gen-sub ⊢e (S≋ Z≋) (s-arr₃ (⊢r-𝕣 (t-⊢r ⊢e₁)) s))) ⊢e₁
gen-sub {j' = ` □} (⊢app {i = ■} ⊢e ⊢e₁) Z≋ s = ⊢app ((gen-sub ⊢e (S≋ Z≋) (s-arr₂ (s-refl-∞ (s-sregular s) (⊢r-𝕣 (t-⊢r ⊢e₁))) s))) ⊢e₁
gen-sub {j' = ` □} (⊢tabs ⊢e) Z≋ s = ⊢sub (⊢tabs ⊢e) s gc-tlam nz-□
gen-sub {j' = ` □} (⊢tapp ⊢e regA st s₁) Z≋ s = ⊢tapp ⊢e regA st (s-trans s₁ Z≋ s)

gen-sub {j' = i · j'} (⊢var regΓ x∈Γ) newj s = ⊢sub (⊢var regΓ x∈Γ) s gc-var nz-app
gen-sub {j' = i · j'} (⊢ann ⊢e) newj s = ⊢sub (⊢ann ⊢e) s gc-ann nz-app
gen-sub {j' = i · j'} (⊢lam₂ ⊢e) (S≋ newj) (s-arr₂ s s₁)
  with reg-S, regΓ regA ← t-tregular ⊢e
  with refl ← s-trans-∞-eq s = ⊢lam₂ (gen-sub ⊢e newj (s1-weaken,0 s₁ regA))
gen-sub {j' = i · j'} (⊢app {i = □} ⊢e ⊢e₁) ~j s = ⊢app (gen-sub ⊢e (S≋ ~j) ((s-arr₃ (⊢r-𝕣 (t-⊢r ⊢e₁)) s))) ⊢e₁
gen-sub {j' = i · j'} (⊢app {i = ■} ⊢e ⊢e₁) ~j s = ⊢app (gen-sub ⊢e (S≋ ~j) ((s-arr₂ (s-refl-∞ (s-sregular s) (⊢r-𝕣 (t-⊢r ⊢e₁))) s))) ⊢e₁
gen-sub {j' = i · j'} (⊢sub ⊢e B≤A gc j≢Z) (S≋ ~j) s = ⊢sub ⊢e (s-trans B≤A (S≋ ~j) s) gc nz-app
gen-sub {j' = i · j'} (⊢tabs {i = ■} ⊢e) newj s = ⊢sub (⊢tabs ⊢e) s gc-tlam nz-app
gen-sub {j' = i · j'} (⊢tapp ⊢e regA st s₁) newj s = ⊢tapp ⊢e regA st (s-trans s₁ newj s)

gen-sub0 : Γ ⊢d `■ # g ⦂ A
         → Γ ⋈ ⊢d j # A ≤ B
         → Γ ⊢d j # g ⦂ B
gen-sub0 ⊢e s = gen-sub ⊢e Z≋ s
