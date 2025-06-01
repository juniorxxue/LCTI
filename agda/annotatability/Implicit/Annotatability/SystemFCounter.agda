module Implicit.Annotatability.SystemFCounter where

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


----------------------------------------------------------------------
--+                             Logic                              +--
----------------------------------------------------------------------

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

data Match : Counter m → Type m → Set where
  m-int : Match (Counter m ∋⦂ Z) Int
  m-var : Match ∞ (‶ X) -- can be case analysis
  m-arr : Match j B
        → Match (𝕚 j) (A `→ B)
  m-∀ : Match (𝕚 j') A
      → (upj : ↑tyʲ0 j ⇘ j')
      → Match (𝕚 j) (`∀ A)


infix 3 _⊢_⦂_⟶_
data _⊢_⦂_⟶_ : Env n m → Term n m → Type m → Counter m × Term n m → Set where

  ela-lit : (regΓ : TRegular Γ)
          → Γ ⊢ (lit n) ⦂ Int ⟶ ⟨ Z , (lit n) ⟩
  ela-var : (regΓ : TRegular Γ)
          → Γ ∋ x ⦂ A
          → Γ ⊢ ` x ⦂ A ⟶ ⟨ Z , ` x ⟩
  ela-lam : Γ , A ⊢ e ⦂ B ⟶ ⟨ j , e' ⟩
          → Γ ⊢ ƛ e ⦂ A `→ B ⟶ ⟨ 𝕚 j , ƛ e' ⟩
  ela-app1 : Γ ⊢ e₁ ⦂ A ⟶ ⟨ Z , e₁' ⟩
           → Γ ⊢ A 𝕄 B `→ C
           → Match (𝕚 j) A
           → Γ ⊢ e₂ ⦂ B ⟶ ⟨ j' , e₂' ⟩
           → Γ ⊢ e₁ · e₂ ⦂ C ⟶ ⟨ j , e₁' · (e₂' ⦂ B) ⟩
  ela-app2 : Γ ⊢ e₁ ⦂ A `→ B ⟶ ⟨ 𝕚 j , e₁' ⟩
           → Γ ⊢ e₂ ⦂ A ⟶ ⟨ j' , e₂' ⟩
           → Γ ⊢ e₁ · e₂ ⦂ B ⟶ ⟨ j , e₁' · (e₂' ⦂ A) ⟩

postulate
    ⊢sub' : Γ ⊢ Z # g ⦂ A
          → (B≤A : Γ ⋈ ⊢ j # A ≤ B)
          → Γ ⊢ j # g ⦂ B


annotatability : Γ ⊢ e ⦂ A ⟶ ⟨ j , e' ⟩
               → Γ ⊢ j # e' ⦂ A
annotatability (ela-lit regΓ) = ⊢lit regΓ
annotatability (ela-var regΓ x) = ⊢var regΓ x
annotatability (ela-lam ⊢e) = ⊢lam₂ (annotatability ⊢e)
annotatability (ela-app1 ⊢e x x₁ ⊢e₁) = ⊢app₂ (⊢sub' (annotatability ⊢e) {!!}) (⊢ann {!annotatability ⊢e₁!})
annotatability (ela-app2 ⊢e ⊢e₁) = ⊢app₂ (annotatability ⊢e) (⊢ann {!annotatability ⊢e₁!})

test : Match (𝕚 j) A
     → Γ ⊢ A 𝕄 B `→ C
     → Γ ⊢ 𝕚 j # A ≤ B `→ C

test' : Γ ⊢ A 𝕄 B
      → Match j A
     → Γ ⊢ j # A ≤ B
test' 𝕄-arr (m-arr mt) = s-arr₂ {!!} (test' {!!} mt)
test' (M-∀ {A = A} x st mm rst) (m-∀ mt upj) with ε-dec {k = #0} {A = A}
... | inj₁ p = s-∀l x st {!!} {!!} {!!} {!!}
... | inj₂ ¬p = {!!}
