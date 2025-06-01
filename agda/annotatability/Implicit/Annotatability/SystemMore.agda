module Implicit.Annotatability.SystemMore where

open import Implicit.Language.All

infix 3 _⊢_#_≤_
data _⊢_#_≤_ : Env n m → Counter m → Type m → Type m → Set where
  s-refl :
      (regΔ : SRegular Δ)
    → (cloA : Δ ⊢r A)
    → Δ ⊢ Z # A ≤ A
  s-int :
      (regΔ : SRegular Δ)
    → Δ ⊢ ∞ # Int ≤ Int
  s-var-∙ :
      (regΔ : SRegular Δ)
    → (inΔ : Δ ∋∙ X)
    → Δ ⊢ ∞ # ‶ X ≤ ‶ X
  s-arr₁ :
      Δ ⊢ ∞ # C ≤ A
    → Δ ⊢ ∞ # B ≤ D
    → Δ ⊢ ∞ # A `→ B ≤ C `→ D
  s-arr₂ :
      Δ ⊢ ∞ # C ≤ A
    → Δ ⊢ j # B ≤ D
    → Δ ⊢ 𝕚 j # A `→ B ≤ C `→ D
  s-arr₃ :
      (regA : Δ ⊢r A)
    → Δ ⊢ j # B ≤ D
    → Δ ⊢ 𝕔 j # A `→ B ≤ A `→ D
  s-∀ :
      Δ ,∙ ⊢ ∞ # A ≤ B
    → Δ ⊢ ∞ # `∀ A ≤ `∀ B
  s-∀l :
      (regB : Γ ⊢r B)
    → (st : ⟦ B ⟧ A ⇘ A*)
    → Γ ⊢ j # A* ≤ C `→ D
    → (ic : (𝕚𝕔 j))
    → (fd : find A #0 j')
    → (upj : ↑tyʲ0 j ⇘ j')
    → Γ ⊢ j # `∀ A ≤ C `→ D
  s-∀l-no :
      (regB : Γ ⊢r B)
    → (st : ⟦ B ⟧ A ⇘ A*)
    → Γ ⊢ j # A* ≤ C `→ D
    → (ic : (𝕚𝕔 j))
    → (nfd : #0 ¬ε A)
    → Γ ⊢ j # `∀ A ≤ C `→ D

s-trans-∞-eq : Γ ⊢ ∞ # A ≤ B
             → A ≡ B
s-trans-∞-eq (s-int regΔ) = refl
s-trans-∞-eq (s-var-∙ regΔ inΔ) = refl
s-trans-∞-eq (s-arr₁ s s₁) = cong₂ _`→_ (sym (s-trans-∞-eq s)) (s-trans-∞-eq s₁)
s-trans-∞-eq (s-∀ s) = cong `∀_ (s-trans-∞-eq s)

s-refl-∞ : SRegular Γ
         → Γ ⊢r A
         → Γ ⊢ ∞ # A ≤ A
s-refl-∞ regΓ ⊢r-int = s-int regΓ
s-refl-∞ regΓ (⊢r-var-∙ inΓ) = s-var-∙ regΓ inΓ
s-refl-∞ regΓ (⊢r-arr regA regA₁) = s-arr₁ (s-refl-∞ regΓ regA) (s-refl-∞ regΓ regA₁)
s-refl-∞ regΓ (⊢r-∀ regA) = s-∀ (s-refl-∞ (reg-S∙ regΓ) regA)

s-sregular : Γ ⊢ j # A ≤ B
           → SRegular Γ
s-sregular (s-refl regΔ cloA) = regΔ
s-sregular (s-int regΔ) = regΔ
s-sregular (s-var-∙ regΔ inΔ) = regΔ
s-sregular (s-arr₁ s s₁) = s-sregular s
s-sregular (s-arr₂ s s₁) = s-sregular s
s-sregular (s-arr₃ regA s) = s-sregular s
s-sregular (s-∀ s) with s-sregular s
... | reg-S∙ r = r
s-sregular (s-∀l regB st s ic fd upj) = s-sregular s
s-sregular (s-∀l-no regB st x ic nfd) = s-sregular x


s1-⊢r-l : Γ ⊢ j # A ≤ B
        → Γ ⊢r A

s1-⊢r-r : Γ ⊢ j # A ≤ B
        → Γ ⊢r B

s1-⊢r-l (s-refl regΔ cloA) = cloA
s1-⊢r-l (s-int regΔ) = ⊢r-int
s1-⊢r-l (s-var-∙ regΔ inΔ) = ⊢r-var-∙ inΔ
s1-⊢r-l (s-arr₁ s s₁) = ⊢r-arr (s1-⊢r-r s) (s1-⊢r-l s₁)
s1-⊢r-l (s-arr₂ s s₁) = ⊢r-arr (s1-⊢r-r s) (s1-⊢r-l s₁)
s1-⊢r-l (s-arr₃ regA s) = ⊢r-arr regA (s1-⊢r-l s)
s1-⊢r-l (s-∀ s) = ⊢r-∀ (s1-⊢r-l s)
s1-⊢r-l (s-∀l regB st s ic fd upj) = st0-⊢r' (s1-⊢r-l s) regB st
s1-⊢r-l (s-∀l-no regB st x ic nfd) = st0-⊢r' (s1-⊢r-l x) regB st

s1-⊢r-r (s-refl regΔ cloA) = cloA
s1-⊢r-r (s-int regΔ) = ⊢r-int
s1-⊢r-r (s-var-∙ regΔ inΔ) = ⊢r-var-∙ inΔ
s1-⊢r-r (s-arr₁ s s₁) = ⊢r-arr (s1-⊢r-l s) (s1-⊢r-r s₁)
s1-⊢r-r (s-arr₂ s s₁) = ⊢r-arr (s1-⊢r-l s) (s1-⊢r-r s₁)
s1-⊢r-r (s-arr₃ regA s) = ⊢r-arr regA (s1-⊢r-r s)
s1-⊢r-r (s-∀ s) = ⊢r-∀ (s1-⊢r-r s)
s1-⊢r-r (s-∀l regB st s ic fd upj) = s1-⊢r-r s
s1-⊢r-r (s-∀l-no regB st x ic nfd) = s1-⊢r-r x

infix 3 _⊢_#_⦂_
data _⊢_#_⦂_ : Env n m → Counter m → Term n m → Type m → Set where
  ⊢lit : ∀ {num : ℕ}
    → (regΓ : TRegular Γ)
    → Γ ⊢ Z # (lit num) ⦂ Int
  ⊢var :
      (regΓ : TRegular Γ)
    → (x∈Γ : Γ ∋ x ⦂ A)
    → Γ ⊢ Z # ` x ⦂ A
  ⊢ann :
      Γ ⊢ ∞ # e ⦂ A
    → Γ ⊢ Z # (e ⦂ A) ⦂ A
  ⊢lam₁ :
      Γ , A ⊢ ∞ # e ⦂ B
    → Γ ⊢ ∞ # ƛ e ⦂ A `→ B
  ⊢lam₂ :
      Γ , A ⊢ j # e ⦂ B
    → Γ ⊢ 𝕚 j # ƛ e ⦂ A `→ B
  ⊢app₁ :
      Γ ⊢ 𝕔 j # e₁ ⦂ A `→ B
    → Γ ⊢ ∞ # e₂ ⦂ A
    → Γ ⊢ j # e₁ · e₂ ⦂ B
  ⊢app₂ :
      Γ ⊢ 𝕚 j # e₁ ⦂ A `→ B
    → Γ ⊢ Z # e₂ ⦂ A
    → Γ ⊢ j # e₁ · e₂ ⦂ B
  ⊢sub :
      Γ ⊢ Z # g ⦂ A
    → (B≤A : Γ ⋈ ⊢ j # A ≤ B)
    → (gc : GenericConsumer g)
    → (j≢Z : NonZ j)
    → Γ ⊢ j # g ⦂ B

posutlate
    ⊢sub' :
      Γ ⊢ Z # g ⦂ A
    → (B≤A : Γ ⋈ ⊢ j # A ≤ B)
    → Γ ⊢ j # g ⦂ B



private variable
  e₁′ : Term n m


t-tregular : Γ ⊢ j # e ⦂ A
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

-- not occur only at the end
infix 3 _¬ε'_
data _¬ε'_ : Fin m → Type m → Set where
  ¬ε'-int : k ¬ε' Int
  ¬ε'-var : k ≢ X
          → k ¬ε' ‶ X
  ¬ε'-arr-l : k ε A
          → k ¬ε' (A `→ B)
  ¬ε'-arr-r : k ¬ε A
            → k ¬ε' B
            → k ¬ε' (A `→ B)
  ¬ε'-∀ : #S k ¬ε' A
        → k ¬ε' (`∀ A)

infix 3 _⊢_𝕄_
data _⊢_𝕄_ : Env n m → Type m → Type m → Set where
  𝕄-arr : Γ ⊢ A `→ B 𝕄 A `→ B
  M-∀ : Γ ⊢r T
      → (st : ⟦ T ⟧ A ⇘ A*)
      → Γ ⊢ A* 𝕄 B `→ C
      → (rst : #0 ¬ε' A)
      → Γ ⊢ `∀ A 𝕄 B `→ C

infix 3 _⊢_⦂_⟶_
data _⊢_⦂_⟶_ : Env n m → Term n m → Type m → Term n m → Set where

  ela-lit : (regΓ : TRegular Γ)
          → Γ ⊢ (lit n) ⦂ Int ⟶ (lit n)
  ela-var : (regΓ : TRegular Γ)
          → Γ ∋ x ⦂ A
          → Γ ⊢ ` x ⦂ A ⟶ ` x
  ela-lam : Γ , A ⊢ e ⦂ B ⟶ e'
          → Γ ⊢ ƛ e ⦂ A `→ B ⟶ ƛ e'
  ela-app : Γ ⊢ e₁ ⦂ A ⟶ e₁'
           → Γ ⊢ A 𝕄 B `→ C
           → Γ ⊢ e₂ ⦂ B ⟶ e₂'
           → Γ ⊢ e₁ · e₂ ⦂ C ⟶ e₁' · (e₂' ⦂ B)

-- f : forall a b. a -> b -> a
-- f 1

-- forall a. a -> (forall b. b -> a)
-- f 1

infix 3 _⊢_⟾_
data _⊢_⟾_ : Env n m → Counter m × Type m → Counter m × Type m → Set where

  base : Γ ⊢ A 𝕄 B
       → Γ ⊢ ⟨ ∞ , A ⟩ ⟾ ⟨ 𝕚 ∞ , B ⟩

  case-𝕚 : Γ ⊢ ⟨ j , B ⟩ ⟾ ⟨ j' , D ⟩
         → Γ ⊢ ⟨ 𝕚 j , A `→ B ⟩ ⟾ ⟨ 𝕚 j' , A `→ D ⟩

  case-𝕔 : Γ ⊢ ⟨ j , B ⟩ ⟾ ⟨ j' , D ⟩
         → Γ ⊢ ⟨ 𝕔 j , A `→ B ⟩ ⟾ ⟨ 𝕔 j' , A `→ D ⟩

⟾-NonZ : NonZ j
       → Γ ⊢ ⟨ j , A ⟩ ⟾ ⟨ j' , B ⟩
       → NonZ j'
⟾-NonZ nz-∞ (base x) = nz-I
⟾-NonZ nz-I (case-𝕚 ~j) = nz-I
⟾-NonZ nz-C (case-𝕔 ~j) = nz-C

𝕄-weaken⋈ : Γ ⊢ A 𝕄 B
          → Γ ⋈ ⊢ A 𝕄 B
𝕄-weaken⋈ 𝕄-arr = 𝕄-arr
𝕄-weaken⋈ (M-∀ x st rst mm) = {!!}
-- M-∀ (⊢r-𝕣 x) st (𝕄-weaken⋈ mm)

⟾-weaken⋈ : Γ ⊢ ⟨ j , A ⟩ ⟾ ⟨ j' , B ⟩
           → Γ ⋈ ⊢ ⟨ j , A ⟩ ⟾ ⟨ j' , B ⟩
⟾-weaken⋈ (base x) = base (𝕄-weaken⋈ x)
⟾-weaken⋈ (case-𝕚 ~j) = case-𝕚 (⟾-weaken⋈ ~j)
⟾-weaken⋈ (case-𝕔 ~j) = case-𝕔 (⟾-weaken⋈ ~j)

𝕄-weaken,0 : Γ ⊢ A 𝕄 B
           → Γ ⊢r T
           → Γ , T ⊢ A 𝕄 B
𝕄-weaken,0 𝕄-arr regT = 𝕄-arr
𝕄-weaken,0 (M-∀ x st rst mm) regT = {!!}
-- M-∀ (⊢r-weaken,0 x regT) st (𝕄-weaken,0 mm regT)

⟾-weaken,0 : Γ ⊢ ⟨ j , A ⟩ ⟾ ⟨ j' , B ⟩
           → Γ ⊢r T
           → Γ , T ⊢ ⟨ j , A ⟩ ⟾ ⟨ j' , B ⟩
⟾-weaken,0 (base x) regT = base (𝕄-weaken,0 x regT)
⟾-weaken,0 (case-𝕚 ~j) regT = case-𝕚 (⟾-weaken,0 ~j regT)
⟾-weaken,0 (case-𝕔 ~j) regT = case-𝕔 (⟾-weaken,0 ~j regT)


⟾-find : find A k j
        → Γ ⊢ ⟨ j , B ⟩ ⟾ ⟨ j' , C ⟩
        → find A k j'
⟾-find (f-∞ x) (base x₁) = {!!}
⟾-find (f-arr-𝕚-l x) (case-𝕚 cv) = f-arr-𝕚-l x
⟾-find (f-arr-𝕚-r ¬inA fd) (case-𝕚 cv) = f-arr-𝕚-r ¬inA (⟾-find fd cv)
⟾-find (f-arr-𝕔 ¬inA fd) (case-𝕔 cv) = f-arr-𝕔 ¬inA (⟾-find fd cv)
⟾-find (f-∀-𝕚 fd upj) (case-𝕚 cv) = f-∀-𝕚 (⟾-find fd (case-𝕚 {!!})) {!!}
⟾-find (f-∀-𝕔 fd upj) (case-𝕔 cv) = f-∀-𝕔 (⟾-find fd (case-𝕔 {!!})) {!!}



test : k ε A
     → k ¬ε' A
     → find A k (𝕚 ∞)
test ε-var (¬ε'-var x) = ⊥-elim (x refl)
test (ε-arr-l inA) ninA = f-arr-𝕚-l inA
test (ε-arr-r ¬inA inA) (¬ε'-arr-l x) = f-arr-𝕚-l x
test (ε-arr-r ¬inA inA) (¬ε'-arr-r x ninA) = f-arr-𝕚-r ¬inA (f-∞ inA)
test (ε-∀ inA) (¬ε'-∀ ninA) = f-∀-𝕚 (test inA ninA) ↑tyʲ-∞

mm-sub : Γ ⊢ A 𝕄 B
       → SRegular Γ
       → Γ ⊢r A
       → Γ ⊢ 𝕚 ∞ # A ≤ B
mm-sub 𝕄-arr regΓ (⊢r-arr regA regA₁) = s-arr₂ (s-refl-∞ regΓ regA) (s-refl-∞ regΓ regA₁)
mm-sub (M-∀ {A = A} x st mm rst) regΓ regA with ε-dec {k = #0} {A = A}
... | inj₁ p = s-∀l x st (mm-sub mm regΓ (st0-⊢r regA x st)) case-𝕚 (test p rst) (↑tyʲ-𝕚 ↑tyʲ-∞)
-- s-∀l x st (mm-sub mm regΓ (st0-⊢r regA x st)) case-𝕚 (f-i∞ p (i∞-i i∞-z)) (↑tyʲ-𝕚 ↑tyʲ-∞)
... | inj₂ ¬p = s-∀l-no x st (mm-sub mm regΓ (st0-⊢r regA x st)) case-𝕚 ¬p
-- s-∀l-no x st (mm-sub mm regΓ (st0-⊢r regA x st)) case-𝕚 ¬p

conv-sub-gen-s : Γ ⊢ j # A ≤ B
               → Γ ⊢ ⟨ j , B ⟩ ⟾ ⟨ j' , C ⟩
               → Γ ⊢ j' # A ≤ C  --- we need to generalize the conclusion

conv-sub-gen-s (s-int regΔ) (base ())
conv-sub-gen-s (s-var-∙ regΔ inΔ) (base ())
conv-sub-gen-s (s-arr₁ s s₁) (base 𝕄-arr) = s-arr₂ s s₁
conv-sub-gen-s (s-arr₂ s s₁) (case-𝕚 cv) = s-arr₂ s (conv-sub-gen-s s₁ cv)
conv-sub-gen-s (s-arr₃ regA s) (case-𝕔 cv) = s-arr₃ regA (conv-sub-gen-s s cv)
conv-sub-gen-s (s-∀ s) (base mm)
  with refl ← s-trans-∞-eq s  = mm-sub mm (s-sregular (s-∀ s)) (⊢r-∀ (s1-⊢r-l s))
conv-sub-gen-s (s-∀l regB st s case-𝕚 fd (↑tyʲ-𝕚 upj)) (case-𝕚 cv) =
  s-∀l regB st (conv-sub-gen-s s (case-𝕚 cv)) case-𝕚 {!!} (↑tyʲ-𝕚 {!!})
conv-sub-gen-s (s-∀l regB st s case-𝕔 fd (↑tyʲ-𝕔 upj)) (case-𝕔 cv) =
  s-∀l regB st (conv-sub-gen-s s (case-𝕔 cv)) case-𝕔 {!!} {!!}
conv-sub-gen-s (s-∀l-no regB st s case-𝕚 fd) (case-𝕚 cv) = s-∀l-no regB st (conv-sub-gen-s s (case-𝕚 cv)) case-𝕚 fd
conv-sub-gen-s (s-∀l-no regB st s case-𝕔 fd) (case-𝕔 cv) = s-∀l-no regB st (conv-sub-gen-s s (case-𝕔 cv)) case-𝕔 fd

conv-sub-gen : Γ ⊢ j # e ⦂ A
             → Γ ⊢ ⟨ j , A ⟩ ⟾ ⟨ j' , B ⟩
             → Γ ⊢ j' # e ⦂ B
conv-sub-gen (⊢lam₁ ⊢e) (base 𝕄-arr) = ⊢lam₂ ⊢e
conv-sub-gen (⊢lam₂ ⊢e) (case-𝕚 cv) with t-tregular ⊢e
... | reg-S, r regA = ⊢lam₂ (conv-sub-gen ⊢e (⟾-weaken,0 cv regA))
conv-sub-gen (⊢app₁ ⊢e ⊢e₁) cv = ⊢app₁ (conv-sub-gen ⊢e (case-𝕔 cv)) ⊢e₁
conv-sub-gen (⊢app₂ ⊢e ⊢e₁) cv = ⊢app₂ (conv-sub-gen ⊢e (case-𝕚 cv)) ⊢e₁
conv-sub-gen (⊢sub ⊢e B≤A gc j≢Z) cv = ⊢sub ⊢e (conv-sub-gen-s B≤A (⟾-weaken⋈ cv)) gc (⟾-NonZ j≢Z cv)

conv-sub : Γ ⊢ ∞ # e ⦂ A
         → Γ ⊢ A 𝕄 B
         → Γ ⊢ 𝕚 ∞ # e ⦂ B
conv-sub ⊢e cv = conv-sub-gen ⊢e (base cv)

conv-sub' : Γ ⊢ ∞ # e ⦂ A
         → Γ ⊢ A 𝕄 B
         → Γ ⊢ 𝕚 ∞ # e ⦂ B
conv-sub' (⊢lam₁ ⊢e) 𝕄-arr = ⊢lam₂ ⊢e
conv-sub' (⊢app₁ ⊢e ⊢e₁) 𝕄-arr = ⊢app₁ {!!} ⊢e₁
conv-sub' (⊢app₁ ⊢e ⊢e₁) (M-∀ x st mm rst) = {!!}
conv-sub' (⊢app₂ ⊢e ⊢e₁) mm = {!!}
conv-sub' (⊢sub ⊢e B≤A gc j≢Z) mm = {!!}

annotatability : Γ ⊢ e ⦂ A ⟶ e'
               → Γ ⊢ ∞ # e' ⦂ A
annotatability (ela-lit reg) = ⊢sub (⊢lit reg) (s-int (reg-Z reg)) gc-i nz-∞
annotatability (ela-var reg x) = ⊢sub (⊢var reg x) (s-refl-∞ (reg-Z reg) (⊢r-𝕣 (∋⦂-⊢r reg x))) gc-var nz-∞
annotatability (ela-lam ⊢e) = ⊢lam₁ (annotatability ⊢e)
annotatability (ela-app ⊢e cv ⊢e₁) = ⊢app₂ {!!} (⊢ann (annotatability ⊢e₁))


-- f : forall a . Int -> a
-- |-8 f 1 : Int -> Int


{-

f 1 : Int -> Int ~~> f (1 : Int)
---------------------------------

(f 1) 2 ---> f 1 2
--------------------

|-I I 8 f :

-}
