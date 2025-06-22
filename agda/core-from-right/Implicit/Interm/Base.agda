module Implicit.Interm.Base where

open import Implicit.Language.All

----------------------------------------------------------------------
--+                           Subtyping                            +--
----------------------------------------------------------------------

infix 3 _⊢_#_⌞_⌝_
data _⊢_#_⌞_⌝_ : Env n m → Counter m → Type m → Polar → Type m → Set where
  s-refl :
      (regΔ : SRegular Δ)
    → (cloA : Δ ⊢c A)
    → (grd : Δ ≫ A ⇘ A%)
    → Δ ⊢ Z # A ⌞ ≤⁺ ⌝ A%
  s-int :
      (regΔ : SRegular Δ)
    → Δ ⊢ ∞ # Int ⌞ ≤ ⌝ Int
  s-var-∙ :
      (regΔ : SRegular Δ)
    → (inΔ : Δ ∋∙ X)
    → Δ ⊢ ∞ # ‶ X ⌞ ≤ ⌝ ‶ X
  s-arr₁ :
      Δ ⊢ ∞ # C ⌞ ⋆ ≤ ⌝ A
    → Δ ⊢ ∞ # B ⌞ ≤ ⌝ D
    → Δ ⊢ ∞ # A `→ B ⌞ ≤ ⌝ C `→ D
  s-arr₂ :
      Δ ⊢ ∞ # C ⌞ ≤⁻ ⌝ A
    → Δ ⊢ j # B ⌞ ≤⁺ ⌝ D
    → Δ ⊢ 𝕚 j # A `→ B ⌞ ≤⁺ ⌝ C `→ D
  s-arr₃ :
      (cloA : Δ ⊢c A)
    → (grd : Δ ≫ A ⇘ A%)
    → Δ ⊢ j # B ⌞ ≤⁺ ⌝ D
    → Δ ⊢ 𝕔 j # A `→ B ⌞ ≤⁺ ⌝ A% `→ D
  s-∀ :
      Δ ,∙ ⊢ ∞ # A ⌞ ≤ ⌝ B
    → Δ ⊢ ∞ # `∀ A ⌞ ≤ ⌝ `∀ B
  s-∀l :
      Δ ,= B ⊢ j' # A ⌞ ≤⁺ ⌝ C' `→ D'
    → (ic : (𝕚𝕔 j))
    → (fd : find A #0 j')
    → (upC : ↑ty0 C ⇘ C')
    → (upD : ↑ty0 D ⇘ D')
    → (upj : ↑tyʲ0 j ⇘ j')
    → Δ ⊢ j # `∀ A ⌞ ≤⁺ ⌝ C `→ D
  s-∀l-no-appear :
      Δ ,^ ⊢ j' # A ⌞ ≤⁺ ⌝ C' `→ D'
    → (ic : (𝕚𝕔 j))
    → (fd : #0 ¬ε A)
    → (upC : ↑ty0 C ⇘ C')
    → (upD : ↑ty0 D ⇘ D')
    → (upj : ↑tyʲ0 j ⇘ j')
    → Δ ⊢ j # `∀ A ⌞ ≤⁺ ⌝ C `→ D
  s-tapp :
      Δ ,= B ⊢ j' # A ⌞ ≤⁺ ⌝ C
    → (upj : ↑tyʲ0 j ⇘ j')
    → Δ ⊢ 𝕥₍ B ₎ j # `∀ A ⌞ ≤⁺ ⌝ `∀ C
  -- two atomic rules
  s-svar-l : ∀ {X A}
    → (SRegular Δ)
    → (inΔ : Δ ∋ X := A)
    → Δ ⊢ ∞ # ‶ X ⌞ ≤⁺ ⌝ A
  s-svar-r : ∀ {X A}
    → (SRegular Δ)
    → (inΔ : Δ ∋ X := A)
    → Δ ⊢ ∞ # A ⌞ ≤⁻ ⌝ ‶ X
  s-svar-𝕚 :
      Δ ∋ X := C
    → Δ ⊢ (𝕚 j) # C ⌞ ≤⁺ ⌝ A `→ B
    → Δ ⊢ (𝕚 j) # ‶ X ⌞ ≤⁺ ⌝ A `→ B
  s-svar-𝕔 :
      Δ ∋ X := C
    → Δ ⊢ (𝕔 j) # C ⌞ ≤⁺ ⌝ A `→ B
    → Δ ⊢ (𝕔 j) # ‶ X ⌞ ≤⁺ ⌝ A `→ B
  s-svar-𝕥 :
      Δ ∋ X := B
    → Δ ⊢ (𝕥₍ A ₎ j) # B ⌞ ≤⁺ ⌝ `∀ C
    → Δ ⊢ (𝕥₍ A ₎ j) # ‶ X ⌞ ≤⁺ ⌝ `∀ C


s-refl-∞ : SRegular Γ
         → Γ ⊢r A
         → Γ ⊢ ∞ # A ⌞ ≤ ⌝ A
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
    → (B≤A : Γ ⋈ ⊢ j # A ⌞ ≤⁺ ⌝ B)
    → (gc : GenericConsumer g)
    → (j≢Z : NonZ j)
    → Γ ⊢ j # g ⦂ B
  ⊢tabs :
      Γ ,∙ ⊢ Z # e ⦂ A
    → Γ ⊢ Z # Λ e ⦂ `∀ A
  ⊢tapp : Γ ⊢ 𝕥₍ A ₎ j # e ⦂ `∀ B
        → (st : ⟦ A ⟧ B ⇘ B*)
        → Γ ⊢ j # e ⓪ A ⦂ B*

-- small note: e @ A must be inferreable, and in the form of
-- (e @ A) e', e' could only be checked
{-
infix 3 _⇉_
data _⇉_ : Counter → Counter → Set where
  ⇉Z : Z ⇉ j
  ⇉I : j ⇉ j′
     → 𝕚 j ⇉ 𝕚 j′
  ⇉IC : j ⇉ j′
     → 𝕚 j ⇉ 𝕔 j′
  ⇉C : j ⇉ j′
     → 𝕔 j ⇉ 𝕔 j′
-}

{-
s-trans : Γ ⊢ j # A ⌞ ≤⁺ ⌝ B
        → j ⇉ j′
        → Γ ⊢ j′ # B ⌞ ≤⁺ ⌝ C
        → Γ ⊢ j′ # A ⌞ ≤⁺ ⌝ C
s-trans (s-refl cloΓ cloA) ⇉Z s2 = s2
s-trans (s-arr₂ opnA s1 s3) (⇉I newj) s2 = {!!}
s-trans (s-∀l s1 ic fd stC stD) (⇉I newj) (s-arr₂ opnA s2 s3) = s-∀l (s-trans s1 (⇉I newj) {!!}) case-𝕚 {!!} {!!} {!!}
s-trans s1 (⇉IC newj) s2 = {!!}
s-trans s1 (⇉C newj) s2 = {!!}
-}


-- sub-gen : Γ ⊢ j # e ⦂ A
--         → j ⇉ j′
--         → Γ ⋈ ⊢ j′ # A ⌞ ≤⁺ ⌝ B
--         → Γ ⊢ j′ # e ⦂ B
-- sub-gen {j′ = Z} ⊢e ⇉Z (s-refl cloΓ cloA) = ⊢e
-- sub-gen {j′ = ∞} (⊢lit cloΓ) ⇉Z s = ⊢sub (⊢lit cloΓ) s gc-i nz-∞
-- sub-gen {j′ = ∞} (⊢var cloΓ x∈Γ) ⇉Z s = ⊢sub (⊢var cloΓ x∈Γ) s gc-var nz-∞
-- sub-gen {j′ = ∞} (⊢ann ⊢e) ⇉Z s = ⊢sub (⊢ann ⊢e) s gc-ann nz-∞
-- sub-gen {j′ = ∞} (⊢app₁ ⊢e ⊢e₁) ⇉Z s = ⊢app₁ (sub-gen ⊢e (⇉C ⇉Z) (s-arr₃ _ s)) ⊢e₁
-- sub-gen {j′ = ∞} (⊢app₂ ⊢e ⊢e₁) ⇉Z s = ⊢app₁ (sub-gen ⊢e (⇉IC ⇉Z) (s-arr₃ _ s)) (sub-gen ⊢e₁ ⇉Z (s-refl-∞ (clo-Z _) _))
-- sub-gen {j′ = ∞} (⊢tabs ⊢e) ⇉Z s = ⊢sub (⊢tabs ⊢e) s gc-tlam nz-∞
-- sub-gen {j′ = 𝕚 j′} (⊢var cloΓ x∈Γ) newj s = ⊢sub (⊢var cloΓ x∈Γ) s gc-var nz-I
-- sub-gen {j′ = 𝕚 j′} (⊢ann ⊢e) newj s = ⊢sub (⊢ann ⊢e) s gc-ann nz-I
-- sub-gen {j′ = 𝕚 j′} (⊢lam₂ ⊢e) (⇉I newj) (s-arr₂ opnA s s₁) = {!!} false
-- sub-gen {j′ = 𝕚 j′} (⊢app₁ ⊢e ⊢e₁) newj s = ⊢app₁ (sub-gen ⊢e (⇉C newj) (s-arr₃ _ s)) ⊢e₁
-- sub-gen {j′ = 𝕚 j′} (⊢app₂ ⊢e ⊢e₁) newj s = ⊢app₁ (sub-gen ⊢e (⇉IC newj) (s-arr₃ _ s)) (sub-gen ⊢e₁ ⇉Z (s-refl-∞ (clo-Z _) _))
-- sub-gen {j′ = 𝕚 j′} (⊢sub ⊢e B≤A x j≢Z) newj s = ⊢sub ⊢e {!!} x nz-I
-- sub-gen {j′ = 𝕚 j′} (⊢tabs ⊢e) newj s = ⊢sub (⊢tabs ⊢e) s gc-tlam nz-I
-- sub-gen {j′ = 𝕔 j′} ⊢e newj s = {!!}
-- {-
-- sub-gen : Γ ⊢ Z # e ⦂ A
--         → Γ ⋈ ⊢ j # A ⌞ ≤⁺ ⌝ B
--         → Γ ⊢ j # e ⦂ B
-- sub-gen {j = Z} ⊢e (s-refl cloΓ cloA) = ⊢e
-- sub-gen {j = ∞} (⊢lit cloΓ) s = ⊢sub (⊢lit cloΓ) s gc-i nz-∞
-- sub-gen {j = ∞} (⊢var cloΓ x∈Γ) s = ⊢sub (⊢var cloΓ x∈Γ) s gc-var nz-∞
-- sub-gen {j = ∞} (⊢ann ⊢e) s = ⊢sub (⊢ann ⊢e) s gc-ann nz-∞
-- sub-gen {j = ∞} (⊢app₁ ⊢e ⊢e₁) s = {!!}
-- sub-gen {j = ∞} (⊢app₂ ⊢e ⊢e₁) s = {!!}
-- sub-gen {j = ∞} (⊢tabs ⊢e) s = ⊢sub (⊢tabs ⊢e) s gc-tlam nz-∞
-- sub-gen {j = 𝕚 j} ⊢e s = {!!}
-- sub-gen {j = 𝕔 j} ⊢e s = {!!}
-- -}

{-
down : Counter (1 + m) → Counter m
down Z = Z
down ∞ = ∞
down (𝕚 j) = 𝕚 (down j)
down (𝕔 j) = 𝕔 (down j)
down (𝕥₍ x ₎ j) = 𝕥₍ Int ₎ (down j)

need : Term n m → Counter m
need (lit i) = Z
need (` x) = Z
need (ƛ e) = 𝕚 (need e)
need (e₁ · e₂) with need e₁
... | Z = Z
... | ∞ = ∞
... | 𝕚 r = r
... | 𝕔 r = r
... | 𝕥₍ A ₎ r = 𝕥₍ A ₎ r
need (e ⦂ A) = Z
need (Λ e) = down (need e)
need (e ⓪ A) = need e

annota : Γ ⊢ j # e ⦂ A
       → need (e) ≡ Z
       → Γ ⊢ Z # e ⦂ A
annota (⊢lit regΓ) refl = ⊢lit regΓ
annota (⊢var regΓ x∈Γ) refl = ⊢var regΓ x∈Γ
annota (⊢ann ⊢e) refl = ⊢ann ⊢e
annota (⊢app₁ {e₁ = e₁} {e₂ = e₂} ⊢e ⊢e₁) eq with need e₁ | annota ⊢e {!!}
... | Z | r = ⊢app₁ {!!} ⊢e₁
... | 𝕚 Z | r = ⊢app₁ {!!} ⊢e₁
... | 𝕔 Z | r = ⊢app₁ {!!} ⊢e₁
annota (⊢app₂ ⊢e ⊢e₁) eq = {!!}
annota (⊢sub ⊢e B≤A gc j≢Z) eq = {!!}
annota (⊢tabs ⊢e) eq = ⊢tabs ⊢e
annota (⊢tapp ⊢e st) eq = {!!}
-}
