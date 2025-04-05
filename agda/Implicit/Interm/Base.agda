module Implicit.Interm.Base where

open import Implicit.Language.All

----------------------------------------------------------------------
--+                           Subtyping                            +--
----------------------------------------------------------------------

infix 3 _⊢_#_⌞_⌝_
data _⊢_#_⌞_⌝_ : Env n m → Counter → Type m → Polar → Type m → Set where
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
      Δ ,= B ⊢ j # A ⌞ ≤⁺ ⌝ C' `→ D'
    → (ic : (𝕚𝕔 j))
    → (fd : find A #0 j)
    → (upC : ↑ty0 C ⇘ C')
    → (upD : ↑ty0 D ⇘ D')
    → Δ ⊢ j # `∀ A ⌞ ≤⁺ ⌝ C `→ D

  -- two atomic rules
  s-svar-l : ∀ {X A}
    → (SRegular Δ)
    → (inΔ : Δ ∋ X := A)
    → Δ ⊢ ∞ # ‶ X ⌞ ≤⁺ ⌝ A
  s-svar-r : ∀ {X A}
    → (SRegular Δ)
    → (inΔ : Δ ∋ X := A)
    → Δ ⊢ ∞ # A ⌞ ≤⁻ ⌝ ‶ X
  -- new rule added
  s-tapp :
      Δ ,≝ B ⊢ j # A ⌞ ≤⁺ ⌝ C
    → Δ ⊢ 𝕥 j # `∀ A ⌞ ≤⁺ ⌝ `∀ C
  s-var-≝ :
      (regΔ : SRegular Δ)
    → (inΔ : Δ ∋≝ X)
    → Δ ⊢ ∞ # ‶ X ⌞ ≤ ⌝ ‶ X
  s-dvar-l : ∀ {X A}
    → (SRegular Δ)
    → (inΔ : Δ ∋ X ≝ A)
    → Δ ⊢ ∞ # ‶ X ⌞ ≤⁺ ⌝ A
  s-dvar-r : ∀ {X A}
    → (SRegular Δ)
    → (inΔ : Δ ∋ X ≝ A)
    → Δ ⊢ ∞ # A ⌞ ≤⁻ ⌝ ‶ X

s-refl-∞ : SRegular Γ
         → Γ ⊢r A
         → Γ ⊢ ∞ # A ⌞ ≤ ⌝ A
s-refl-∞ regΓ ⊢r-int = s-int regΓ
s-refl-∞ regΓ (⊢r-var-∙ inΓ) = s-var-∙ regΓ inΓ
s-refl-∞ regΓ (⊢r-var-≝ inΓ) = s-var-≝ regΓ inΓ
s-refl-∞ regΓ (⊢r-arr regA regA₁) = s-arr₁ (s-refl-∞ regΓ regA) (s-refl-∞ regΓ regA₁)
s-refl-∞ regΓ (⊢r-∀ regA) = s-∀ (s-refl-∞ (reg-S∙ regΓ) regA)

----------------------------------------------------------------------
--+                             Typing                             +--
----------------------------------------------------------------------

infix 3 _⊢_#_⦂_
data _⊢_#_⦂_ : Env n m → Counter → Term n m → Type m → Set where
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
  ⊢tapp :
      Γ ⊢ (𝕥 j) # e ⦂ `∀ B
    → (regA : Γ ⊢r A)
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


_ : ∅ ⊢ Z # ((Λ ((ƛ (` #0)) ⦂ (‶ #0 `→ ‶ #0))) ⓪ Int) · (lit 1) ⦂ Int
_ = ⊢app₁ (⊢tapp (⊢sub (⊢tabs
                         (⊢ann
                          (⊢lam₁
                           (⊢sub (⊢var (reg-S, (reg-S∙ reg-Z) (⊢r-var-∙ Z)) Z)
                            (s-var-∙ (reg-Z (reg-S, (reg-S∙ reg-Z) (⊢r-var-∙ Z))) (S⋈ (S, Z)))
                            gc-var nz-∞))))
                            (s-tapp (s-arr₃ (⊢c-var-≝ Z) (grd-var≝ Z) (s-refl (reg-S≝ (reg-Z reg-Z) ⊢r-int) (⊢c-var-≝ Z) (grd-var≝ Z))))
                            gc-tlam
                            nz-T) ⊢r-int (st-arr (st-var stx-eq) (st-var stx-eq)))
          (⊢sub (⊢lit reg-Z) (s-int (reg-Z reg-Z)) gc-i nz-∞)


f-type : Type 0
f-type = `∀ `∀ (‶ #1 `→ ‶ #0) `→ Int

ann-id : Term 1 0
ann-id = (ƛ (` #0)) ⦂ Int `→ Int

dumb-type : Type 0
dumb-type = Int `→ Int `→ Int `→ Int `→ Int


_ : (∅ , f-type) ⊢ Z # ((` #0) ⓪ dumb-type) · ann-id ⦂ Int
_ = ⊢app₂ (⊢tapp (⊢sub (⊢var
                         (reg-S, reg-Z
                          (⊢r-∀
                           (⊢r-∀ (⊢r-arr (⊢r-arr (⊢r-var-∙ (S∙ Z)) (⊢r-var-∙ Z)) ⊢r-int))))
                         Z) (s-tapp {B = Int} (s-∀l {B = Int} (s-arr₂
                                                                (s-arr₁
                                                                 (s-dvar-l
                                                                  (reg-S=
                                                                   (reg-S≝
                                                                    (reg-Z
                                                                     (reg-S, reg-Z
                                                                      (⊢r-∀
                                                                       (⊢r-∀ (⊢r-arr (⊢r-arr (⊢r-var-∙ (S∙ Z)) (⊢r-var-∙ Z)) ⊢r-int)))))
                                                                    ⊢r-int)
                                                                   ⊢r-int)
                                                                  (S= (Z ↑ty-int) ↑ty-int))
                                                                 (s-svar-r
                                                                  (reg-S=
                                                                   (reg-S≝
                                                                    (reg-Z
                                                                     (reg-S, reg-Z
                                                                      (⊢r-∀
                                                                       (⊢r-∀ (⊢r-arr (⊢r-arr (⊢r-var-∙ (S∙ Z)) (⊢r-var-∙ Z)) ⊢r-int)))))
                                                                    ⊢r-int)
                                                                   ⊢r-int)
                                                                  (Z ↑ty-int)))
                                                                (s-refl
                                                                 (reg-S=
                                                                  (reg-S≝
                                                                   (reg-Z
                                                                    (reg-S, reg-Z
                                                                     (⊢r-∀
                                                                      (⊢r-∀ (⊢r-arr (⊢r-arr (⊢r-var-∙ (S∙ Z)) (⊢r-var-∙ Z)) ⊢r-int)))))
                                                                   ⊢r-int)
                                                                  ⊢r-int)
                                                                 ⊢c-int grd-int)) case-𝕚 (f-arr-𝕚-l (ε-arr-r (¬ε-var (λ ())) ε-var)) (↑ty-arr ↑ty-int ↑ty-int) ↑ty-int))
                         gc-var nz-T)
          (⊢r-arr ⊢r-int
                  (⊢r-arr ⊢r-int (⊢r-arr ⊢r-int (⊢r-arr ⊢r-int ⊢r-int)))) (st-arr (st-arr st-int st-int) st-int))
          (⊢ann
            (⊢lam₁
             (⊢sub
              (⊢var
               (reg-S,
                (reg-S, reg-Z
                 (⊢r-∀
                  (⊢r-∀ (⊢r-arr (⊢r-arr (⊢r-var-∙ (S∙ Z)) (⊢r-var-∙ Z)) ⊢r-int))))
                ⊢r-int)
               Z)
              (s-int
               (reg-Z
                (reg-S,
                 (reg-S, reg-Z
                  (⊢r-∀
                   (⊢r-∀ (⊢r-arr (⊢r-arr (⊢r-var-∙ (S∙ Z)) (⊢r-var-∙ Z)) ⊢r-int))))
                 ⊢r-int)))
              gc-var nz-∞)))
