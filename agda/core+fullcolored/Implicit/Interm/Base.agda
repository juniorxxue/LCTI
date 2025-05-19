module Implicit.Interm.Base where

open import Implicit.Language.All

----------------------------------------------------------------------
--+                           Subtyping                            +--
----------------------------------------------------------------------

infix 3 _⊢_#_⌞_⌝_
data _⊢_#_⌞_⌝_ : Env n m → Counter m → Type m → Polar → Type m → Set where
  s-refl+ :
      (regΔ : SRegular Δ)
    → (cloA : Δ ⊢c A)
    → (grd : Δ ≫ A ⇘ A%)
    → Δ ⊢ `𝕫 # A ⌞ ≤⁺ ⌝ A%
  s-refl- :
      (regΔ : SRegular Δ)
    → (cloA : Δ ⊢c A)
    → (grd : Δ ≫ A ⇘ A%)
    → Δ ⊢ `𝕫 # A% ⌞ ≤⁻ ⌝ A
  s-int :
      (regΔ : SRegular Δ)
    → Δ ⊢ `∞ # Int ⌞ ≤ ⌝ Int
  s-var-∙ :
      (regΔ : SRegular Δ)
    → (inΔ : Δ ∋∙ X)
    → Δ ⊢ `∞ # ‶ X ⌞ ≤ ⌝ ‶ X
  s-arr₁ :
      Δ ⊢ `∞ # C ⌞ ⋆ ≤ ⌝ A
    → Δ ⊢ `∞ # B ⌞ ≤ ⌝ D
    → Δ ⊢ `∞ # A `→ B ⌞ ≤ ⌝ C `→ D
  s-arr₂ :
      Δ ⊢ 𝔼 𝕖 # C ⌞ ≤⁻ ⌝ A
    → Δ ⊢ j # B ⌞ ≤⁺ ⌝ D
    → Δ ⊢ 𝕊₍ 𝕖 ₎ j # A `→ B ⌞ ≤⁺ ⌝ C `→ D
  s-arr-n :
      Δ ⊢ `∞ # C ⌞ ≤⁺ ⌝ A
    → Δ ⊢ `𝕟 i # B ⌞ ≤⁻ ⌝ D
    → Δ ⊢ `𝕟 (suc i) # A `→ B ⌞ ≤⁻ ⌝ C `→ D
  s-∀ :
      Δ ,∙ ⊢ `∞ # A ⌞ ≤ ⌝ B
    → Δ ⊢ `∞ # `∀ A ⌞ ≤ ⌝ `∀ B
  s-∀l :
      Δ ,= B ⊢ (𝕊₍ 𝕖 ₎ j') # A ⌞ ≤⁺ ⌝ C' `→ D'
--    → (fd : find2 A #0 (𝕊₍ w' ₎ j'))
    → (upC : ↑ty0 C ⇘ C')
    → (upD : ↑ty0 D ⇘ D')
    → (upj : ↑tyʲ0 j ⇘ j')
    → Δ ⊢ (𝕊₍ 𝕖 ₎ j) # `∀ A ⌞ ≤⁺ ⌝ C `→ D
  s-tapp :
      Δ ,= B ⊢ j' # A ⌞ ≤⁺ ⌝ C
    → (upj : ↑tyʲ0 j ⇘ j')
    → Δ ⊢ 𝕋₍ B ₎ j # `∀ A ⌞ ≤⁺ ⌝ `∀ C
  -- two atomic rules
  s-svar-l : ∀ {X A}
    → (SRegular Δ)
    → (inΔ : Δ ∋ X := A)
    → Δ ⊢ `∞ # ‶ X ⌞ ≤⁺ ⌝ A
  s-svar-r : ∀ {X A}
    → (SRegular Δ)
    → (inΔ : Δ ∋ X := A)
    → Δ ⊢ `∞ # A ⌞ ≤⁻ ⌝ ‶ X

s-refl-∞ : SRegular Γ
         → Γ ⊢r A
         → Γ ⊢ `∞ # A ⌞ ≤ ⌝ A
s-refl-∞ regΓ ⊢r-int = s-int regΓ
s-refl-∞ regΓ (⊢r-var-∙ inΓ) = s-var-∙ regΓ inΓ
s-refl-∞ regΓ (⊢r-arr regA regA₁) = s-arr₁ (s-refl-∞ regΓ regA) (s-refl-∞ regΓ regA₁)
s-refl-∞ regΓ (⊢r-∀ regA) = s-∀ (s-refl-∞ (reg-S∙ regΓ) regA)

----------------------------------------------------------------------
--+                             Typing                             +--
----------------------------------------------------------------------

infix 3 _⊢_#_⦂_
data _⊢_#_⦂_ : Env n m → Counter m → Term n m → Type m → Set where
  ⊢lit : ∀ {num : ℕ}
    → (regΓ : TRegular Γ)
    → Γ ⊢ `𝕫 # (lit num) ⦂ Int
  ⊢var :
      (regΓ : TRegular Γ)
    → (x∈Γ : Γ ∋ x ⦂ A)
    → Γ ⊢ `𝕫 # ` x ⦂ A
  ⊢ann :
      Γ ⊢ `∞ # e ⦂ A
    → Γ ⊢ `𝕫 # (e ⦂ A) ⦂ A
  ⊢lam₁ :
      Γ , A ⊢ `∞ # e ⦂ B
    → Γ ⊢ `∞ # ƛ e ⦂ A `→ B
  ⊢lam₂ :
      Γ , A ⊢ j # e ⦂ B
    → Γ ⊢ 𝕊₍ 𝕟 0 ₎ j # ƛ e ⦂ A `→ B
  ⊢lam₃ :
      Γ , A ⊢ 𝔼 (𝕟 i) # e ⦂ B
    → Γ ⊢ 𝔼 (𝕟 (suc i)) # ƛ e ⦂ A `→ B
  ⊢app :
      Γ ⊢ 𝕊₍ 𝕖 ₎ j # e₁ ⦂ A `→ B
    → Γ ⊢ 𝔼 𝕖 # e₂ ⦂ A
    → Γ ⊢ j # e₁ · e₂ ⦂ B
  ⊢sub :
      Γ ⊢ `𝕫 # g ⦂ A
    → (B≤A : Γ ⋈ ⊢ j # A ⌞ ≤⁺ ⌝ B)
    → (gc : GenericConsumer g)
    → (j≢Z : NonZ j)
    → Γ ⊢ j # g ⦂ B
  ⊢tabs :
      Γ ,∙ ⊢ `𝕫 # e ⦂ A
    → Γ ⊢ `𝕫 # Λ e ⦂ `∀ A
  ⊢tapp : Γ ⊢ 𝕋₍ A ₎ j # e ⦂ `∀ B
        → (st : ⟦ A ⟧ B ⇘ B*)
        → Γ ⊢ j # e ⓪ A ⦂ B*


data Match1 : Type m → ℕ → Set where
  m1-z : Match1 A 0
  m1-s : Match1 B i
       → Match1 (A `→ B) (suc i)

data Match2 : Type m → ENat → Set where
  m2-∞ : Match2 A ∞
  m2-n : Match1 A i
       → Match2 A (𝕟 i)

data Match : Type m → Counter m → Set where
  m-𝔼 : Match2 A 𝕖
      → Match A (𝔼 𝕖)
  m-𝕊 : Match2 A 𝕖
      → Match B j
      → Match (A `→ B) (𝕊₍ 𝕖 ₎ j)
  𝕞-𝕋 : Match A* j
      → (st : ⟦ B ⟧ A ⇘ A*)
      → Match (`∀ A) (𝕋₍ B ₎ j)

postulate
  s-match+ : Γ ⊢ j # A ⌞ ≤⁺ ⌝ B
        → Match B j

  s-match- : Γ ⊢ j # A ⌞ ≤⁻ ⌝ B
        → Match A j
{-
s-match+ (s-refl+ regΔ cloA grd) = m-𝔼 (m2-n m1-z)
s-match+ (s-int regΔ) = m-𝔼 m2-∞
s-match+ (s-var-∙ regΔ inΔ) = m-𝔼 m2-∞
s-match+ (s-arr₁ s s₁) = m-𝔼 m2-∞
s-match+ (s-arr₂ s s₁) with s-match- s
... | m-𝔼 x = m-𝕊 x (s-match+ s₁)
s-match+ (s-∀ s) = m-𝔼 m2-∞
s-match+ (s-∀l s upC upD upj) = m-𝕊 {!!} {!!}
s-match+ (s-tapp s upj) = 𝕞-𝕋 {!!} {!!}
s-match+ (s-svar-l x inΔ) = m-𝔼 m2-∞

s-match- (s-refl- regΔ cloA grd) = m-𝔼 (m2-n m1-z)
s-match- (s-int regΔ) = m-𝔼 m2-∞
s-match- (s-var-∙ regΔ inΔ) = m-𝔼 m2-∞
s-match- (s-arr₁ s s₁) = m-𝔼 m2-∞
s-match- (s-arr-n s s₁) with s-match- s₁
... | m-𝔼 (m2-n x) = m-𝔼 (m2-n (m1-s x))
s-match- (s-∀ s) = m-𝔼 m2-∞
s-match- (s-svar-r x inΔ) = m-𝔼 m2-∞
-}


t-match : Γ ⊢ j # e ⦂ A
        → Match A j

t-match (⊢lit regΓ) = m-𝔼 (m2-n m1-z)
t-match (⊢var regΓ x∈Γ) = m-𝔼 (m2-n m1-z)
t-match (⊢ann ⊢e) = m-𝔼 (m2-n m1-z)
t-match (⊢lam₁ ⊢e) = m-𝔼 m2-∞
t-match (⊢lam₂ ⊢e) = m-𝕊 (m2-n m1-z) (t-match ⊢e)
t-match (⊢lam₃ ⊢e) with t-match ⊢e
... | m-𝔼 (m2-n mt) = m-𝔼 (m2-n (m1-s mt))
t-match (⊢app ⊢e ⊢e₁) with t-match ⊢e
... | m-𝕊 x r = r
t-match (⊢sub ⊢e B≤A gc j≢Z) = s-match+ B≤A
t-match (⊢tabs ⊢e) = m-𝔼 (m2-n m1-z)
t-match (⊢tapp ⊢e st) with t-match ⊢e
... | 𝕞-𝕋 r st₁
  with refl ← st-unique st st₁ = r
