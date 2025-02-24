module Implicit.Interm.Base where

open import Implicit.Language.All

----------------------------------------------------------------------
--+                           Subtyping                            +--
----------------------------------------------------------------------

infix 3 _⊢_#_⌞_⌝_
data _⊢_#_⌞_⌝_ : Env n m → Counter → Type m → Polar → Type m → Set where
  s-refl :
      (cloΓ : SubClosed Γ)
    → (cloA : Γ ⊢c A)
    → Γ ⊢ Z # A ⌞ ≤⁺ ⌝ A
  s-int :
      (cloΓ : SubClosed Γ)
    → Γ ⊢ ∞ # Int ⌞ ≤ ⌝ Int
  s-var-∙ :
      (cloΓ : SubClosed Γ)
    → (inΓ : Γ ∋∙ X)
    → Γ ⊢ ∞ # ‶ X ⌞ ≤ ⌝ ‶ X
  s-var-= :  -- this rule can subsumed by last two rules, but requiring finding a good measure, keep them now
      (cloΓ : SubClosed Γ)
    → (inΓ : Γ ∋=¹ X)
    → Γ ⊢ ∞ # ‶ X ⌞ ≤ ⌝ ‶ X
  s-arr₁ :
      Γ ⊢ ∞ # C ⌞ ⋆ ≤ ⌝ A
    → Γ ⊢ ∞ # B ⌞ ≤ ⌝ D
    → Γ ⊢ ∞ # A `→ B ⌞ ≤ ⌝ C `→ D
  s-arr₂ :
      (opnA : Γ ⊢o²' A)
    → Γ ⊢ ∞ # C ⌞ ≤⁻ ⌝ A
    → Γ ⊢ j # B ⌞ ≤⁺ ⌝ D
    → Γ ⊢ 𝕚 j # A `→ B ⌞ ≤⁺ ⌝ C `→ D
  s-arr₃ :
      (cloA : Γ ⊢c A)
    → Γ ⊢ j # B ⌞ ≤⁺ ⌝ D
    → Γ ⊢ 𝕔 j # A `→ B ⌞ ≤⁺ ⌝ A `→ D
  s-∀ :
      Γ ,∙ ⊢ ∞ # A ⌞ ≤ ⌝ B
    → Γ ⊢ ∞ # `∀ A ⌞ ≤ ⌝ `∀ B
  s-∀l :
      Γ ,= B ⊢ j # A ⌞ ≤⁺ ⌝ C `→ D
  -- we guess a solution of B here, we must make sure this B is provided from the counter
  -- what we does is to make sure the all inputs matching the counter should at least have the quantifer contained
    → (ic : (𝕚𝕔 j))
    → (fd : find A #0 j)
    → (stC : ⟦ B ⟧ C ⇘ C*)
    → (stD : ⟦ B ⟧ D ⇘ D*)
    → Γ ⊢ j # `∀ A ⌞ ≤⁺ ⌝ C* `→ D*
  -- two atomic rules
  s-var-sub-l : ∀ {X A}
    → (cloA : Γ ⊢c¹ A)
    → (inΓ : Γ ∋ X :=² A)
--    → Γ ⊢ ∞ # B ⌞ ≤⁺ ⌝ A
    → Γ ⊢ ∞ # ‶ X ⌞ ≤⁺ ⌝ A
  s-var-sub-r : ∀ {X A}
    → (cloA : Γ ⊢c¹ A)
    → (inΓ : Γ ∋ X :=² A)
--    → Γ ⊢ ∞ # A ⌞ ≤⁻ ⌝ B
    → Γ ⊢ ∞ # A ⌞ ≤⁻ ⌝ ‶ X
  s-var-typ-l : ∀ {X A B}
    → (inΓ : Γ ∋ X :=¹ B)
    → Γ ⊢ ∞ # B ⌞ ≤ ⌝ A
    → Γ ⊢ ∞ # ‶ X ⌞ ≤ ⌝ A
  s-var-typ-r : ∀ {X A B}
    → (inΓ : Γ ∋ X :=¹ B)
    → Γ ⊢ ∞ # A ⌞ ≤ ⌝ B
    → Γ ⊢ ∞ # A ⌞ ≤ ⌝ ‶ X

s-refl-∞ : SubClosed Γ
         → Γ ⊢c¹ A
         → Γ ⊢ ∞ # A ⌞ ≤ ⌝ A
s-refl-∞ cloΓ ⊢c¹-int = s-int cloΓ
s-refl-∞ cloΓ (⊢c¹-var-∙ inΓ) = s-var-∙ cloΓ inΓ
s-refl-∞ cloΓ (⊢c¹-var-= inΓ) = s-var-= cloΓ inΓ
s-refl-∞ cloΓ (⊢c¹-arr cloA cloA₁) = s-arr₁ (s-refl-∞ cloΓ cloA) (s-refl-∞ cloΓ cloA₁)
s-refl-∞ cloΓ (⊢c¹-∀ cloA) = s-∀ (s-refl-∞ (clo-S∙ cloΓ) cloA)

----------------------------------------------------------------------
--+                             Typing                             +--
----------------------------------------------------------------------

infix 3 _⊢_#_⦂_
data _⊢_#_⦂_ : Env n m → Counter → Term n m → Type m → Set where
  ⊢lit : ∀ {num : ℕ}
    → (cloΓ : TypClosed Γ)
    → Γ ⊢ Z # (lit num) ⦂ Int
  ⊢var :
      (cloΓ : TypClosed Γ)
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
    → GenericConsumer g
    → (j≢Z : NonZ j)
    → Γ ⊢ j # g ⦂ B
  ⊢tabs :
      Γ ,∙ ⊢ Z # e ⦂ A
    → Γ ⊢ Z # Λ e ⦂ `∀ A

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
