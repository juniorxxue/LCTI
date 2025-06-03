module Implicit.Algo.Base where

open import Implicit.Language.All

open import Implicit.Algo.Constructs.Syntax public
open import Implicit.Algo.Constructs.Shift public
open import Implicit.Algo.Constructs.Subst public
open import Implicit.Algo.Constructs.Lookup public

infix 3 _⊢_⌞_⌝_⊣_
data _⊢_⌞_⌝_⊣_ : Env n m → Type m → Polar → Type m → Env n m → Set where
  s-int :
      (regΓ : SRegular Δ)
    → Δ ⊢ Int ⌞ ≤ ⌝ Int ⊣ Δ

  s-var-∙ :
      (regΓ : SRegular Δ)
    → Δ ∋∙ X
    → Δ ⊢ (‶ X) ⌞ ≤ ⌝ (‶ X) ⊣ Δ

  s-ex-l^ :
--      (x-in : Δ ∋^ X)
--    → (regA : Δ ⊢r A)
      (inst : [ A / X ] Δ ⟹ Ψ)
    → Δ ⊢ ‶ X ⌞ ≤⁺ ⌝ A ⊣ Ψ

  s-ex-r^ :
--      (x-in : Δ ∋^ X) -- implied by inst
--    → (regA : Γ ⊢r A) -- implied by the inst
      (inst : [ A / X ] Δ ⟹ Ψ)
    → Δ ⊢ A ⌞ ≤⁻ ⌝ (‶ X) ⊣ Ψ

  s-ex-l= :
      (regΓ : SRegular Δ)
    → (x-in : Δ ∋ X := A)
    → Δ ⊢ ‶ X ⌞ ≤⁺ ⌝ A ⊣ Δ

  s-ex-r= :
      (regΓ : SRegular Δ)
    → (x-in : Δ ∋ X := A)
    → Δ ⊢ A ⌞ ≤⁻ ⌝ (‶ X) ⊣ Δ

  s-arr :
      Δ ⊢ C ⌞ ⋆ ≤ ⌝ A ⊣ Ω
    → Ω ⊢ B ⌞ ≤ ⌝ D ⊣ Ψ
    → Δ ⊢ A `→ B ⌞ ≤ ⌝ (C `→ D) ⊣ Ψ

  s-∀ :
      Δ ,∙ ⊢ A ⌞ ≤ ⌝ B ⊣ Ψ ,∙
    → Δ ⊢ `∀ A ⌞ ≤ ⌝ (`∀ B) ⊣ Ψ

infix 3 _⊢_⇒_⇒_
infix 3 _⊢_≤⁺_⊣_↪_
infix 3 _⊨_⟹_

data _⊢_⇒_⇒_ : Env n m → Context n m → Term n m → Type m → Set
data _⊢_≤⁺_⊣_↪_ : Env n m → Type m → Context n m → Env n m → Type m → Set
data _⊨_⟹_ : Env n m → Context n m → Type m → Set

data _⊢_⇒_⇒_ where

  ⊢lit : ∀ {num : ℕ}
    → (regΓ : TRegular Γ)
    → Γ ⊢ □ ⇒ lit num ⇒ Int

  ⊢var :
      (regΓ : TRegular Γ)
    → (x∈Γ : Γ ∋ x ⦂ A)
    → Γ ⊢ □ ⇒ ` x ⇒ A

  ⊢ann :
      Γ ⊢ τ A ⇒ e ⇒ B
    → Γ ⊢ □ ⇒ e ⦂ A ⇒ A

  ⊢app :
      Γ ⊢ [ e₂ ]↝ Σ ⇒ e₁ ⇒ A `→ B
    → Γ ⊢ Σ ⇒ e₁ · e₂ ⇒ B

  ⊢lam₁ :
      Γ , A ⊢ τ B ⇒ e ⇒ C
    → Γ ⊢ τ (A `→ B) ⇒ ƛ e ⇒ A `→ C

  ⊢lam₂ :
      Γ ⊢ □ ⇒ e₂ ⇒ A
    → (up-c : ↑tmᶜ0 Σ ⇘ Σ')
    → Γ , A ⊢ Σ' ⇒ e ⇒ B
    → Γ ⊢ [ e₂ ]↝ Σ ⇒ ƛ e ⇒ A `→ B

  ⊢sub :
      Γ ⊢ □ ⇒ g ⇒ A
    → (ne : NonEmpty Σ)
    → (gc : GenericConsumer g)
    → (s : Γ ⋈ ⊢ A ≤⁺ Σ ⊣ Γ ⋈ ↪ B)
    → Γ ⊢ Σ ⇒ g ⇒ B

  ⊢tabs :
      Γ ,∙ ⊢ □ ⇒ e ⇒ A
    → Γ ⊢ □ ⇒ Λ e ⇒ `∀ A

  ⊢tapp :
      Γ ⊢ A ⓪↝ Σ ⇒ e ⇒ `∀ B
    → (st : ⟦ A ⟧ B ⇘ B*)
    → Γ ⊢ Σ ⇒ e ⓪ A ⇒ B*

data _⊢_≤⁺_⊣_↪_ where

  s-empty :
      (regΓ : SRegular Δ)
    → (cloA : Δ ⊢c A)
    → (grd : Δ ≫ A ⇘ A%)
    → Δ ⊢ A ≤⁺ □ ⊣ Δ ↪ A%

  s-type :
      (ss : Δ ⊢ A ⌞ ≤⁺ ⌝ B ⊣ Ψ)
    → Δ ⊢ A ≤⁺ (τ B) ⊣ Ψ ↪ B

  s-term-c :
      (cloA : Δ ⊢c A)
    → (ap : Δ ≫ A ⇘ A%)
    → (⊢e : 𝕣 Δ ⊢ τ A% ⇒ e ⇒ A')
    → Δ ⊢ B ≤⁺ Σ ⊣ Ψ ↪ D
    → Δ ⊢ (A `→ B) ≤⁺ ([ e ]↝ Σ) ⊣ Ψ ↪ A% `→ D

  s-term-o :
      (opnA : Δ ⊢o A)
    → (⊢e : 𝕣 Δ ⊢ □ ⇒ e ⇒ C)
    → (ss : Δ ⊢ C ⌞ ≤⁻ ⌝ A ⊣ Ω)
    → Ω ⊢ B ≤⁺ Σ ⊣ Ψ ↪ D
    → Δ ⊢ A `→ B ≤⁺ ([ e ]↝ Σ) ⊣ Ψ ↪ C `→ D

  s-∀l :
      Δ ,^ ⊢ A ≤⁺ ([ e' ]↝ Σ') ⊣ Ψ ,= B ↪ (C' `→ D')
    → (upᶜ : ↑tyᶜ0 Σ ⇘ Σ')
    → (upᵉ : ↑tyᵉ0 e ⇘ e')
    → (upC : ↑ty0 C ⇘ C')
    → (upD : ↑ty0 D ⇘ D')
    → Δ ⊢ `∀ A ≤⁺ ([ e ]↝ Σ) ⊣ Ψ ↪ C `→ D

  s-tapp :
      Δ ,= B ⊢ A ≤⁺ Σ' ⊣ Ψ ,= B ↪ C
    → (upᶜ : ↑tyᶜ0 Σ ⇘ Σ')
    → Δ ⊢ `∀ A ≤⁺ (B ⓪↝ Σ) ⊣ Ψ ↪ `∀ C

  s-svar-term :
      Δ ∋ X := A
    → Δ ⊢ A ≤⁺ ([ e ]↝ Σ) ⊣ Δ ↪ B `→ C
    → Δ ⊢ ‶ X ≤⁺ ([ e ]↝ Σ) ⊣ Δ ↪ B `→ C

  s-svar-tapp :
      Δ ∋ X := A
    → Δ ⊢ A ≤⁺ (B ⓪↝ Σ) ⊣ Δ ↪ `∀ C
    → Δ ⊢ ‶ X ≤⁺ (B ⓪↝ Σ) ⊣ Δ ↪ `∀ C

  s-evar-infers :
      (infs : 𝕣 Δ ⊨ [ e ]↝ Σ ⟹ A)
    → (inst : [ A / X ] Δ ⟹ Ψ) -- implies Γ ∋^k
    → Δ ⊢ ‶ X ≤⁺ ([ e ]↝ Σ) ⊣ Ψ ↪ A

data _⊨_⟹_ where
  infs-z : (regΓ : TRegular Γ)
         → (regA : Γ ⊢r A)
         → Γ ⊨ τ A ⟹ A
  infs-s : (⊢e : Γ ⊢ □ ⇒ e ⇒ A)
         → Γ ⊨ Σ ⟹ B
         → Γ ⊨ [ e ]↝ Σ ⟹ A `→ B

_ : ∅ , (Int `→ Int) , `∀ (‶ #0 `→ ‶ #0) ⊢ □ ⇒ (` #0 · ` #1) · (lit 1) ⇒ Int
_ = ⊢app (⊢app (⊢sub (⊢var (reg-S, (reg-S, reg-Z (⊢r-arr ⊢r-int ⊢r-int))
                             (⊢r-∀ (⊢r-arr (⊢r-var-∙ Z) (⊢r-var-∙ Z)))) Z)
                             ne-app gc-var
                             (s-∀l (s-term-o (⊢o-var-^ Z) (⊢var (reg-S^
                                                                  (reg-S, (reg-S, reg-Z (⊢r-arr ⊢r-int ⊢r-int))
                                                                   (⊢r-∀ (⊢r-arr (⊢r-var-∙ Z) (⊢r-var-∙ Z)))))
                                                                   (S^ (S, Z) (↑ty-arr ↑ty-int ↑ty-int))) (s-ex-r^
                                                                                                            (⟹^0 (↑ty-arr ↑ty-int ↑ty-int) (⊢r-arr ⊢r-int ⊢r-int)
                                                                                                             (reg-Z
                                                                                                              (reg-S, (reg-S, reg-Z (⊢r-arr ⊢r-int ⊢r-int))
                                                                                                               (⊢r-∀ (⊢r-arr (⊢r-var-∙ Z) (⊢r-var-∙ Z)))))))
                                                     (s-svar-term (Z (↑ty-arr ↑ty-int ↑ty-int))
                                                     (s-term-c ⊢c-int grd-int (⊢sub
                                                                                (⊢lit
                                                                                 (reg-S=
                                                                                  (reg-S, (reg-S, reg-Z (⊢r-arr ⊢r-int ⊢r-int))
                                                                                   (⊢r-∀ (⊢r-arr (⊢r-var-∙ Z) (⊢r-var-∙ Z))))
                                                                                  (⊢r-arr ⊢r-int ⊢r-int)))
                                                                                ne-τ gc-i
                                                                                (s-type
                                                                                 (s-int
                                                                                  (reg-Z
                                                                                   (reg-S=
                                                                                    (reg-S, (reg-S, reg-Z (⊢r-arr ⊢r-int ⊢r-int))
                                                                                     (⊢r-∀ (⊢r-arr (⊢r-var-∙ Z) (⊢r-var-∙ Z))))
                                                                                    (⊢r-arr ⊢r-int ⊢r-int))))))
                                                                                    (s-empty
                                                                                      (reg-S=
                                                                                       (reg-Z
                                                                                        (reg-S, (reg-S, reg-Z (⊢r-arr ⊢r-int ⊢r-int))
                                                                                         (⊢r-∀ (⊢r-arr (⊢r-var-∙ Z) (⊢r-var-∙ Z)))))
                                                                                       (⊢r-arr ⊢r-int ⊢r-int))
                                                                                      ⊢c-int grd-int)))) (↑tyᶜ-e ↑tyᵉ-lit ↑tyᶜ-□) ↑tyᵉ-var (↑ty-arr ↑ty-int ↑ty-int)
                                                                                      (↑ty-arr ↑ty-int ↑ty-int))))
